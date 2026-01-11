pub struct Type {
    name: String,
}

impl Type {
    pub fn new(name: &str) -> Self {
        Type {
            name: name.to_string(),
        }
    }
}
