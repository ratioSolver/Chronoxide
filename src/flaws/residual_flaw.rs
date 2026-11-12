use crate::graph::{FlawId, ResolverId};

pub(crate) struct ResidualFlaw {
    id: FlawId,

    causes: Vec<ResolverId>,
    required_by: Vec<ResolverId>,
    resolvers: Vec<ResolverId>,
}
