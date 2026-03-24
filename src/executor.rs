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
        let (tx, mut rx) = mpsc::unbounded_channel();
        let event_bus = ExecutorEventBus::new();

        tokio::spawn(async move {
            loop {
                tokio::select! {
                    Some(cmd) = rx.recv() => {
                        handle_command(cmd).await;
                    }
                }
            }
        });

        Self { tx, event_bus }
    }
}

async fn handle_command(cmd: ExecutorCommand) {
    match cmd {
        ExecutorCommand::ReadRiDDle { script, resp } => {}
    }
}
