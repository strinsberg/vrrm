// An assembler for the virtual machine from a string to byte code.
// Very simple for now.

pub enum Ast {
    Keyword(String),
    List(Vec<Ast>),
}
