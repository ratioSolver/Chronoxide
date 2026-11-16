use tracing::subscriber;
use tracing_subscriber::EnvFilter;

#[tokio::main]
async fn main() {
    subscriber::set_global_default(tracing_subscriber::fmt().with_env_filter(EnvFilter::try_from_default_env().unwrap_or_else(|_| EnvFilter::new("info"))).finish()).expect("Failed to set global default subscriber");
}
