use crate::flaws::ResolverId;
use crate::solver_state::SolverState;
use crate::{ToJson, flaws::FlawId};
use serde_json::Value;
use tokio::sync::{broadcast, mpsc, oneshot};

type CommandResult<T> = oneshot::Sender<Result<T, SolverError>>;

enum SolverCommand {
    ReadRiDDle(String, CommandResult<()>),
    Solve(CommandResult<()>),
    ToJson(CommandResult<Value>),
}

#[derive(Debug)]
pub enum SolverError {
    RuntimeError(String),
    Inconsistent,
}

#[derive(Clone)]
pub enum SolverEvent {
    NewFlaw(Value),
    FlawCostUpdate(Value),
    FlawStatusUpdate(Value),
    CurrentFlaw(Option<FlawId>),
    NewResolver(Value),
    ResolverStatusUpdate(Value),
    CurrentResolver(Option<ResolverId>),
}

#[derive(Clone)]
pub struct Solver {
    tx_cmd: mpsc::Sender<SolverCommand>,
    pub tx_event: broadcast::Sender<SolverEvent>,
}

impl Default for Solver {
    fn default() -> Self {
        Self::new()
    }
}

impl Solver {
    pub fn new() -> Self {
        let (tx_cmd, mut rx_cmd) = mpsc::channel(100);
        let (tx_event, _) = broadcast::channel(100);
        let tx_event_clone = tx_event.clone();
        tokio::task::spawn_blocking(move || {
            let state = SolverState::new(tx_event_clone);

            while let Some(cmd) = rx_cmd.blocking_recv() {
                match cmd {
                    SolverCommand::ReadRiDDle(riddle, responder) => match state.read(&riddle) {
                        Ok(_) => {
                            let _ = responder.send(Ok(()));
                        }
                        Err(e) => {
                            let _ = responder.send(Err(e));
                        }
                    },
                    SolverCommand::Solve(responder) => match state.solve() {
                        true => {
                            let _ = responder.send(Ok(()));
                        }
                        false => {
                            let _ = responder.send(Err(SolverError::Inconsistent));
                        }
                    },
                    SolverCommand::ToJson(responder) => {
                        let json = state.to_json();
                        let _ = responder.send(Ok(json));
                    }
                }
            }
        });
        Self { tx_cmd, tx_event }
    }

    pub async fn read(&self, riddle: String) -> Result<(), SolverError> {
        let (reply_tx, reply_rx) = oneshot::channel();
        self.tx_cmd.send(SolverCommand::ReadRiDDle(riddle, reply_tx)).await.map_err(|_| SolverError::Inconsistent)?;
        reply_rx.await.map_err(|_| SolverError::Inconsistent)?
    }

    pub async fn solve(&self) -> Result<(), SolverError> {
        let (reply_tx, reply_rx) = oneshot::channel();
        self.tx_cmd.send(SolverCommand::Solve(reply_tx)).await.map_err(|_| SolverError::Inconsistent)?;
        reply_rx.await.map_err(|_| SolverError::Inconsistent)?
    }

    pub async fn to_json(&self) -> Result<Value, SolverError> {
        let (reply_tx, reply_rx) = oneshot::channel();
        self.tx_cmd.send(SolverCommand::ToJson(reply_tx)).await.map_err(|_| SolverError::Inconsistent)?;
        reply_rx.await.map_err(|_| SolverError::Inconsistent)?
    }
}
