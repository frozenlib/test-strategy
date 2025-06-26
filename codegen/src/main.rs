mod arbitrary_in_macro_rules;
mod utils;
fn main() -> anyhow::Result<()> {
    arbitrary_in_macro_rules::build()?;
    Ok(())
}
