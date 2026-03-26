use crate::{Solver, solver::SolverEvent};
use riddle::serde_json::Value;
use std::sync::{Arc, Mutex};
use tokio::sync::{mpsc, oneshot};
use tracing::debug;

enum ExecutorCommand {
    ReadRiDDle { script: String, resp: oneshot::Sender<Result<(), String>> },
    Snapshot { resp: oneshot::Sender<Value> },
    StartTimer,
    StopTimer,
}

#[derive(Clone, Debug)]
pub enum ExecutorEvent {
    ProblemSolved(Value),
    NewFlaw(Value),
    NewResolver(Value),
}

#[derive(Clone)]
pub struct ExecutorEventBus {
    subscribers: Arc<Mutex<Vec<mpsc::UnboundedSender<ExecutorEvent>>>>,
}

impl ExecutorEventBus {
    fn new() -> Self {
        Self { subscribers: Arc::new(Mutex::new(Vec::new())) }
    }

    pub fn subscribe(&self) -> mpsc::UnboundedReceiver<ExecutorEvent> {
        let (tx, rx) = mpsc::unbounded_channel();
        self.subscribers.lock().expect("CoCo event subscriber list mutex poisoned").push(tx);
        rx
    }

    pub fn send(&self, event: ExecutorEvent) {
        let mut subscribers = self.subscribers.lock().expect("CoCo event subscriber list mutex poisoned");
        subscribers.retain(|tx| tx.send(event.clone()).is_ok());
    }
}

pub struct Executor {
    tx: mpsc::UnboundedSender<ExecutorCommand>,
    event_bus: ExecutorEventBus,
}

impl Executor {
    pub fn new() -> Self {
        let (tx, mut rx) = mpsc::unbounded_channel::<ExecutorCommand>();
        let event_bus = ExecutorEventBus::new();
        let event_bus_task = event_bus.clone();

        std::thread::spawn(move || {
            let rt = tokio::runtime::Builder::new_current_thread().enable_all().build().expect("Failed to build single-thread Tokio runtime for Executor");

            rt.block_on(async move {
                let slv = Solver::new();
                let mut slv_rx = slv.get_event_sender().subscribe();
                let mut timer_handle: Option<tokio::task::JoinHandle<()>> = None;

                loop {
                    tokio::select! {
                        cmd = rx.recv() => match cmd {
                            Some(ExecutorCommand::ReadRiDDle { script, resp }) => {
                                slv.read(&script);
                                let _ = resp.send(Ok(()));
                            }
                            Some(ExecutorCommand::Snapshot { resp }) => {
                                let _ = resp.send(slv.to_json());
                            }
                            Some(ExecutorCommand::StartTimer) => {
                                if timer_handle.is_none() {
                                    timer_handle = Some(tokio::spawn(async move {
                                        let mut interval = tokio::time::interval(std::time::Duration::from_secs(1));
                                        loop {
                                            interval.tick().await;
                                            debug!("Timer tick");
                                        }
                                    }));
                                }
                            }
                            Some(ExecutorCommand::StopTimer) => {
                                if let Some(handle) = timer_handle.take() {
                                    handle.abort();
                                }
                            }
                            None => break,
                        },
                        event = slv_rx.recv() => match event {
                            Some(SolverEvent::NewFlaw(flaw)) => {
                                event_bus_task.send(ExecutorEvent::NewFlaw(flaw.to_json()));
                            }
                            Some(SolverEvent::NewResolver(resolver)) => {
                                event_bus_task.send(ExecutorEvent::NewResolver(resolver.to_json()));
                            }
                            None => break,
                        },
                    }
                }
            });
        });

        Self { tx, event_bus }
    }

    pub fn get_event_sender(&self) -> ExecutorEventBus {
        self.event_bus.clone()
    }

    pub async fn read(&self, script: String) -> Result<(), String> {
        let (resp_tx, resp_rx) = oneshot::channel();
        self.tx.send(ExecutorCommand::ReadRiDDle { script, resp: resp_tx }).expect("Executor actor thread has stopped");
        resp_rx.await.expect("Executor actor thread has stopped")
    }

    pub fn start_timer(&self) {
        self.tx.send(ExecutorCommand::StartTimer).expect("Executor actor thread has stopped");
    }

    pub fn stop_timer(&self) {
        self.tx.send(ExecutorCommand::StopTimer).expect("Executor actor thread has stopped");
    }

    pub async fn to_json(&self) -> Value {
        let (resp_tx, resp_rx) = oneshot::channel();
        self.tx.send(ExecutorCommand::Snapshot { resp: resp_tx }).expect("Executor actor thread has stopped");
        resp_rx.await.expect("Executor actor thread has stopped")
    }
}
