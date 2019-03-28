use crate::{
    context::{Context, PavoResult},
    gc_foreign::Vector,
    value::Value,
};

pub fn eq(a: &Value, b:  &Value, _: &mut Context) -> PavoResult {
    a.pavo_eq(b)
}

pub fn arr_new(inners: &[Value], _: &mut Context) -> PavoResult {
    let mut v = Vector::new();

    for inner in inners {
        v.push_back(inner.clone())
    }

    Ok(Value::new_array(v))
}
