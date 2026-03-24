use crate::Solver;
use std::sync::{Arc, Mutex};
use tokio::sync::{mpsc, oneshot};

pub enum ExecutorCommand {
    ReadRiDDle { script: String, resp: oneshot::Sender<Result<(), String>> },
}

#[derive(Clone, Debug)]
pub enum ExecutorEvent {
    ProblemSolved,
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

        std::thread::spawn(move || {
            let rt = tokio::runtime::Builder::new_current_thread().enable_all().build().expect("Failed to build single-thread Tokio runtime for Executor");

            rt.block_on(async move {
                let slv = Solver::new();
                let mut slv_rx = slv.get_event_sender().subscribe();

                loop {
                    tokio::select! {
                        cmd = rx.recv() => match cmd {
                            Some(ExecutorCommand::ReadRiDDle { script, resp }) => {
                                slv.read(&script);
                                let _ = resp.send(Ok(()));
                            }
                            None => break,
                        },
                        event = slv_rx.recv() => match event {
                            Some(_solver_event) => {
                                // forward solver events to the executor event bus if needed
                                // event_bus_actor.send(ExecutorEvent::ProblemSolved);
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

    pub async fn read_riddle(&self, script: String) -> Result<(), String> {
        let (resp_tx, resp_rx) = oneshot::channel();
        self.tx.send(ExecutorCommand::ReadRiDDle { script, resp: resp_tx }).expect("Executor actor thread has stopped");
        resp_rx.await.expect("Executor actor thread has stopped")
    }
}
