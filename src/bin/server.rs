use std::sync::Arc;

use axum::{
    Router,
    extract::{State, WebSocketUpgrade, ws::WebSocket},
    response::IntoResponse,
    routing::get,
};
use tower_http::services::{ServeDir, ServeFile};

struct AppState {}

#[tokio::main]
async fn main() {
    let app_state = Arc::new(AppState {});

    let app = Router::new()
        .route("/ws", get(ws_handler))
        .with_state(app_state)
        .nest_service("/assets", ServeDir::new("gui/app/dist/assets"))
        .fallback_service(
            ServeDir::new("gui/app/dist")
                .not_found_service(ServeFile::new("gui/app/dist/index.html")),
        );

    let listener = tokio::net::TcpListener::bind("0.0.0.0:3000").await.unwrap();
    axum::serve(listener, app).await.unwrap();
}

async fn ws_handler(ws: WebSocketUpgrade, State(state): State<Arc<AppState>>) -> impl IntoResponse {
    ws.on_upgrade(move |socket| handle_socket(socket, state))
}

async fn handle_socket(mut _socket: WebSocket, _state: Arc<AppState>) {}
