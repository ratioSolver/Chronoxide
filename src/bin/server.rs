use axum::{
    Router,
    extract::{
        State, WebSocketUpgrade,
        ws::{Message, WebSocket},
    },
    response::IntoResponse,
    routing::get,
};
use chronoxide::{Solver, SolverEventBus};
use std::sync::Arc;
use tokio::sync::broadcast::error::RecvError;
use tower_http::services::{ServeDir, ServeFile};

#[derive(Clone)]
struct AppState {
    event_bus: SolverEventBus,
}

#[tokio::main]
async fn main() {
    let slv = Solver::new();
    let event_bus = slv.get_event_sender();
    let app_state = Arc::new(AppState { event_bus });

    let app = Router::new().route("/ws", get(ws_handler)).with_state(app_state).nest_service("/assets", ServeDir::new("gui/app/dist/assets")).fallback_service(ServeDir::new("gui/app/dist").not_found_service(ServeFile::new("gui/app/dist/index.html")));

    let listener = tokio::net::TcpListener::bind("0.0.0.0:3000").await.unwrap();
    axum::serve(listener, app).await.unwrap();
}

async fn ws_handler(ws: WebSocketUpgrade, State(state): State<Arc<AppState>>) -> impl IntoResponse {
    ws.on_upgrade(move |socket| handle_socket(socket, state))
}

async fn handle_socket(mut socket: WebSocket, state: Arc<AppState>) {
    let mut rx = state.event_bus.subscribe();
    loop {
        match rx.recv().await {
            Ok(msg) => {
                if socket.send(Message::Text(msg.into())).await.is_err() {
                    break;
                }
            }
            Err(RecvError::Lagged(_)) => continue,
            Err(RecvError::Closed) => break,
        }
    }
}
