use axum::{
    Router,
    extract::{
        State, WebSocketUpgrade,
        ws::{Message, WebSocket},
    },
    response::IntoResponse,
    routing::get,
};
use chronoxide::{Solver, solver::SolverEventBus};
use std::sync::Arc;
use tokio::sync::Notify;
use tower_http::services::{ServeDir, ServeFile};

#[derive(Clone)]
struct AppState {
    event_bus: SolverEventBus,
    first_client_connected: Arc<Notify>,
}

#[tokio::main]
async fn main() {
    let args = std::env::args().collect::<Vec<_>>();
    if args.len() < 2 {
        eprintln!("Usage: {} <files>", args[0]);
        std::process::exit(1);
    }

    let files = args[1..].to_vec();

    let slv = Solver::new();
    let app_state = Arc::new(AppState { event_bus: slv.get_event_sender(), first_client_connected: Arc::new(Notify::new()) });
    let read_state = app_state.clone();

    let app = Router::new().route("/ws", get(ws_handler)).with_state(app_state).nest_service("/assets", ServeDir::new("gui/app/dist/assets")).fallback_service(ServeDir::new("gui/app/dist").not_found_service(ServeFile::new("gui/app/dist/index.html")));

    let listener = tokio::net::TcpListener::bind("0.0.0.0:3000").await.unwrap();
    let server = tokio::spawn(async move {
        axum::serve(listener, app).await.unwrap();
    });

    // Parse only after at least one websocket client is connected.
    read_state.first_client_connected.notified().await;
    for file in &files {
        slv.read(&std::fs::read_to_string(file).expect("Failed to read file"));
    }

    server.await.unwrap();
}

async fn ws_handler(ws: WebSocketUpgrade, State(state): State<Arc<AppState>>) -> impl IntoResponse {
    ws.on_upgrade(move |socket| handle_socket(socket, state))
}

async fn handle_socket(mut socket: WebSocket, state: Arc<AppState>) {
    let mut rx = state.event_bus.subscribe();
    state.first_client_connected.notify_waiters();
    while let Some(msg) = rx.recv().await {
        if socket.send(Message::Text(msg.into())).await.is_err() {
            return;
        }
    }
}
