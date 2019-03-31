use crate::{
    context::{Context, PavoResult},
    gc_foreign::Vector,
    value::Value,
};

fn as_int(v: &Value) -> Result<i64, Value> {
    match v {
        Value::Int(n) => Ok(*n),
        _ => Err(Value::new_nil()), // XXX
    }
}

pub fn as_arr(v: &Value) -> Result<Vector<Value>, Value> {
    match v {
        Value::Array(arr) => Ok(arr.clone()),
        _ => Err(Value::new_nil()), // XXX
    }
}

pub fn eq(a: &Value, b: &Value, _: &mut Context) -> PavoResult {
    Ok(Value::new_bool(a == b))
}

pub fn arr_new(inners: &[Value], _: &mut Context) -> PavoResult {
    let mut v = Vector::new();

    for inner in inners {
        v.push_back(inner.clone())
    }

    Ok(Value::new_array(v))
}

pub fn arr_get(v: &Value, index: &Value, _: &mut Context) -> PavoResult {
    let arr = as_arr(v)?;
    let n = as_int(index)? as usize;

    match arr.get(n) {
        Some(got) => Ok(got.clone()),
        None => Err(Value::new_nil()), // XXX
    }
}

pub fn arr_get_or_nil(v: &Value, index: &Value, cx: &mut Context) -> PavoResult {
    match arr_get(v, index, cx) {
        Ok(yay) => Ok(yay),
        Err(..) => Ok(Value::new_nil()),
    }
}

pub fn assert_arr_len_at_most(v: &Value, len: &Value, _: &mut Context) -> PavoResult {
    let arr = as_arr(v)?;
    let n = as_int(len)? as usize;

    if arr.len() <= n {
        Ok(Value::new_nil())
    } else {
        Err(Value::new_nil()) // XXX
    }
}

// pub fn arr_splice_suffix(v: &Value, from: &Value, _: &mut Context) -> PavoResult {
//     let arr = as_arr(v)?;
//     let n = as_int(from)? as usize;
//
//     if n > arr.len() {
//         return Err(Value::new_nil()); // XXX
//     }
//
//     Ok(Value::new_array(arr.skip(n)))
// }

// This "helpfully" returns an empty array on index-out-of-bounds. Not exposed as a toplevel
// function, but used in the desugaring of array patterns.
pub fn arr_splice_suffix_helpful(v: &Value, from: &Value, _: &mut Context) -> PavoResult {
    let arr = as_arr(v)?;
    let n = as_int(from)? as usize;

    if n > arr.len() {
        return Ok(Value::new_array(Vector::new()))
    }

    Ok(Value::new_array(arr.skip(n)))
}

pub fn assert_arr(v: &Value, _: &mut Context) -> PavoResult {
    let _ = as_arr(v)?;
    Ok(Value::new_nil())
}
