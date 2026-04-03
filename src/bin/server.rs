use std::sync::Arc;

use axum::{
    Router,
    extract::{
        State, WebSocketUpgrade,
        ws::{Message, WebSocket},
    },
    response::IntoResponse,
    routing::get,
};
use chronoxide::solver::{Solver, SolverEvent};
use riddle::serde_json;
use tokio::sync::Notify;
use tower_http::services::{ServeDir, ServeFile};
use tracing::{Level, error, subscriber};

#[derive(Clone)]
struct AppState {
    slv: Solver,
    first_client_connected: Arc<Notify>,
}

#[tokio::main]
async fn main() {
    let subscriber = tracing_subscriber::fmt().with_max_level(Level::TRACE).finish();
    subscriber::set_global_default(subscriber).expect("Failed to set global default subscriber");

    let args = std::env::args().collect::<Vec<_>>();
    if args.len() < 2 {
        error!("Usage: {} <files>", args[0]);
        std::process::exit(1);
    }

    let files = args[1..].to_vec();

    let slv = Solver::new();
    let app_state = AppState { slv: slv.clone(), first_client_connected: Arc::new(Notify::new()) };

    let app = Router::new().route("/ws", get(ws_handler)).with_state(app_state.clone()).nest_service("/assets", ServeDir::new("gui/app/dist/assets")).fallback_service(ServeDir::new("gui/app/dist").not_found_service(ServeFile::new("gui/app/dist/index.html")));

    let listener = tokio::net::TcpListener::bind("0.0.0.0:3000").await.unwrap();
    let server = tokio::spawn(async move {
        axum::serve(listener, app).await.unwrap();
    });

    app_state.first_client_connected.notified().await;
    for file in &files {
        slv.read(std::fs::read_to_string(file).expect("Failed to read file")).await.expect("Failed to read RiDDle script");
    }

    server.await.unwrap();
}

async fn ws_handler(ws: WebSocketUpgrade, State(state): State<AppState>) -> impl IntoResponse {
    ws.on_upgrade(move |socket| handle_socket(socket, state))
}

async fn handle_socket(mut socket: WebSocket, state: AppState) {
    let mut rx = state.slv.tx_event.subscribe();

    let mut msg = state.slv.to_json().await.expect("Failed to serialize solver state to JSON");
    msg["msg_type"] = "status".into();
    if socket.send(Message::Text(serde_json::to_string(&msg).unwrap().into())).await.is_err() {
        return;
    }

    state.first_client_connected.notify_waiters();
    while let Ok(event) = rx.recv().await {
        let send_result = match event {
            SolverEvent::NewFlaw(flaw) => {
                let mut msg = flaw;
                msg["msg_type"] = "new-flaw".into();
                socket.send(Message::Text(serde_json::to_string(&msg).unwrap().into())).await
            }
            SolverEvent::NewResolver(resolver) => {
                let mut msg = resolver;
                msg["msg_type"] = "new-resolver".into();
                socket.send(Message::Text(serde_json::to_string(&msg).unwrap().into())).await
            }
        };
        if send_result.is_err() {
            break;
        }
    }
}
