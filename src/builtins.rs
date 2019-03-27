use crate::{
    context::{Context, PavoResult},
    value::Value,
};

pub fn eq(a: &Value, b:  &Value, _: &mut Context) -> PavoResult {
    a.pavo_eq(b)
}
