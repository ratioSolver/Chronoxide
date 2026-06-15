use axum::{
    Router,
    extract::{
        State, WebSocketUpgrade,
        ws::{Message, WebSocket},
    },
    response::IntoResponse,
    routing::get,
};
use chronoxide::{
    ToJson,
    solver::{Solver, SolverEvent},
};
use serde_json::{Value, json};
use std::sync::Arc;
use tokio::sync::{Notify, broadcast::error::RecvError};
use tower_http::services::{ServeDir, ServeFile};
use tracing::{Level, error, subscriber, trace};

#[derive(Clone)]
struct AppState {
    slv: Solver,
    first_client_connected: Arc<Notify>,
}

#[tokio::main(flavor = "current_thread")]
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
    match slv.solve().await {
        Ok(_) => trace!("Solver finished successfully"),
        Err(e) => error!("Solver failed with error: {:?}", e),
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
    loop {
        tokio::select! {
            incoming = socket.recv() => {
                match incoming {
                    Some(Ok(Message::Close(_))) | None => break,
                    Some(Ok(Message::Ping(payload))) => {
                        if socket.send(Message::Pong(payload)).await.is_err() {
                            break;
                        }
                    }
                    Some(Ok(_)) => {}
                    Some(Err(_)) => break,
                }
            }
            recv = rx.recv() => {
                let event = match recv {
                    Ok(event) => event,
                    Err(RecvError::Lagged(skipped)) => {
                        trace!("WebSocket client lagging behind, skipped {} events", skipped);
                        continue;
                    }
                    Err(RecvError::Closed) => break,
                };

                let send_result = match event {
                    SolverEvent::NewFlaw{  flaw_id,  phi, causes, supports, status, cost, data } => {
                        let mut msg = json!({
                            "msg_type": "new-flaw",
                            "id": format!("{}", flaw_id),
                            "phi": format!("{}", phi),
                            "causes": causes.iter().map(|id| format!("{}", id)).collect::<Vec<_>>(),
                            "supports": supports.iter().map(|id| format!("{}", id)).collect::<Vec<_>>(),
                            "status": status.to_json(),
                            "cost": cost.to_json()
                        });
                        msg.as_object_mut().unwrap().extend(data.as_object().unwrap().clone());
                        socket.send(Message::Text(serde_json::to_string(&msg).unwrap().into())).await
                    }
                    SolverEvent::FlawCostUpdate { flaw_id, cost } => {
                        let msg = json!({
                            "msg_type": "flaw-cost-update",
                            "id": format!("{}", flaw_id),
                            "cost": cost.to_json(),
                        });
                        socket.send(Message::Text(serde_json::to_string(&msg).unwrap().into())).await
                    }
                    SolverEvent::FlawStatusUpdate { flaw_id, status } => {
                        let msg = json!({
                            "msg_type": "flaw-status-update",
                            "id": format!("{}", flaw_id),
                            "status": status.to_json(),
                        });
                        socket.send(Message::Text(serde_json::to_string(&msg).unwrap().into())).await
                    }
                    SolverEvent::CurrentFlaw(flaw_id) => {
                        let msg = json!({
                            "msg_type": "current-flaw",
                            "id": flaw_id.map(|id| Value::String(format!("{}", id))).unwrap_or(Value::Null),
                        });
                        socket.send(Message::Text(serde_json::to_string(&msg).unwrap().into())).await
                    }
                    SolverEvent::NewResolver { resolver_id, rho, flaw_id, requirements, intrinsic_cost, status, data } => {
                        let mut msg = json!({
                            "msg_type": "new-resolver",
                            "id": format!("{}", resolver_id),
                            "rho": format!("{}", rho),
                            "flaw_id": format!("{}", flaw_id),
                            "requirements": requirements.iter().map(|id| format!("{}", id)).collect::<Vec<_>>(),
                            "intrinsic_cost": intrinsic_cost.to_json(),
                            "status": status.to_json(),
                        });
                        msg.as_object_mut().unwrap().extend(data.as_object().unwrap().clone());
                        socket.send(Message::Text(serde_json::to_string(&msg).unwrap().into())).await
                    }
                    SolverEvent::ResolverStatusUpdate { resolver_id, status } => {
                        let msg = json!({
                            "msg_type": "resolver-status-update",
                            "id": format!("{}", resolver_id),
                            "status": status.to_json(),
                        });
                        socket.send(Message::Text(serde_json::to_string(&msg).unwrap().into())).await
                    }
                    SolverEvent::CurrentResolver(resolver_id) => {
                        let msg = json!({
                            "msg_type": "current-resolver",
                            "id": resolver_id.map(|id| Value::String(format!("{}", id))).unwrap_or(Value::Null),
                        });
                        socket.send(Message::Text(serde_json::to_string(&msg).unwrap().into())).await
                    }
                };
                if send_result.is_err() {
                    break;
                }
            }
        }
    }
}
