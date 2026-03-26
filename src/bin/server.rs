use axum::{
    Router,
    extract::{
        State, WebSocketUpgrade,
        ws::{Message, WebSocket},
    },
    response::IntoResponse,
    routing::get,
};
use chronoxide::{Executor, executor::ExecutorEvent};
use riddle::serde_json;
use std::sync::Arc;
use tokio::sync::Notify;
use tower_http::services::{ServeDir, ServeFile};
use tracing::Level;

#[derive(Clone)]
struct AppState {
    exec: Arc<Executor>,
    first_client_connected: Arc<Notify>,
}

#[tokio::main]
async fn main() {
    let subscriber = tracing_subscriber::fmt().with_max_level(Level::TRACE).finish();
    tracing::subscriber::set_global_default(subscriber).expect("Failed to set global default subscriber");

    let args = std::env::args().collect::<Vec<_>>();
    if args.len() < 2 {
        eprintln!("Usage: {} <files>", args[0]);
        std::process::exit(1);
    }

    let files = args[1..].to_vec();

    let exec = Arc::new(Executor::new());
    let app_state = Arc::new(AppState { exec: exec.clone(), first_client_connected: Arc::new(Notify::new()) });
    let read_state = app_state.clone();

    let app = Router::new().route("/ws", get(ws_handler)).with_state(app_state).nest_service("/assets", ServeDir::new("gui/app/dist/assets")).fallback_service(ServeDir::new("gui/app/dist").not_found_service(ServeFile::new("gui/app/dist/index.html")));

    let listener = tokio::net::TcpListener::bind("0.0.0.0:3000").await.unwrap();
    let server = tokio::spawn(async move {
        axum::serve(listener, app).await.unwrap();
    });

    // Parse only after at least one websocket client is connected.
    read_state.first_client_connected.notified().await;
    for file in &files {
        exec.read(std::fs::read_to_string(file).expect("Failed to read file")).await.expect("Failed to read RiDDle script");
    }

    server.await.unwrap();
}

async fn ws_handler(ws: WebSocketUpgrade, State(state): State<Arc<AppState>>) -> impl IntoResponse {
    ws.on_upgrade(move |socket| handle_socket(socket, state))
}

async fn handle_socket(mut socket: WebSocket, state: Arc<AppState>) {
    let mut rx = state.exec.get_event_sender().subscribe();

    let mut msg = state.exec.to_json().await;
    msg["msg_type"] = "state".into();
    if socket.send(Message::Text(serde_json::to_string(&msg).unwrap().into())).await.is_err() {
        return;
    }

    state.first_client_connected.notify_waiters();
    while let Some(msg) = rx.recv().await {
        let send_result = match msg {
            ExecutorEvent::ProblemSolved(solver) => {
                let mut msg = solver;
                msg["msg_type"] = "problem_solved".into();
                socket.send(Message::Text(serde_json::to_string(&msg).unwrap().into())).await
            }
            ExecutorEvent::NewFlaw(flaw) => {
                let mut msg = flaw;
                msg["msg_type"] = "new_flaw".into();
                socket.send(Message::Text(serde_json::to_string(&msg).unwrap().into())).await
            }
            ExecutorEvent::NewResolver(resolver) => {
                let mut msg = resolver;
                msg["msg_type"] = "new_resolver".into();
                socket.send(Message::Text(serde_json::to_string(&msg).unwrap().into())).await
            }
        };
        if send_result.is_err() {
            break;
        }
    }
}
