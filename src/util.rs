use std::{
    fmt,
    cmp::Ordering,
};

use nom::types::CompleteStr;
use nom_locate::LocatedSpan;

type Span<'a> = LocatedSpan<CompleteStr<'a>>;

#[derive(PartialEq, Eq, Debug, Clone, Copy, Hash, PartialOrd, Ord)]
pub struct SrcLocation {
    offset: usize,
    line: u32,
    col: usize,
}

impl Default for SrcLocation {
    fn default() -> Self {
        SrcLocation {
            offset: 0,
            line: 0,
            col: 0
        }
    }
}

impl SrcLocation {
    pub fn from_span(span: &Span<'_>) -> SrcLocation {
        SrcLocation {
            offset: span.offset,
            line: span.line,
            col: span.get_utf8_column(),
        }
    }
}

pub struct FnWrap<Fun>(pub Fun);

impl<A, B, C, Z> fmt::Debug for FnWrap<fn(&A, &B, &mut C) -> Z> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        (self.0 as *const ()).fmt(f)
    }
}

impl<A, B, C, Z> Clone for FnWrap<fn(&A, &B, &mut C) -> Z> {
    fn clone(&self) -> Self {
        FnWrap(self.0.clone())
    }
}

impl<A, B, C, Z> Copy for FnWrap<fn(&A, &B, &mut C) -> Z> {}

impl<A, B, C, Z> PartialEq for FnWrap<fn(&A, &B, &mut C) -> Z> {
    fn eq(&self, other: &Self) -> bool {
        self.0 as usize == other.0 as usize
    }
}

impl<A, B, C, Z> Eq for FnWrap<fn(&A, &B, &mut C) -> Z> {}

impl<A, B, C, Z> Ord for FnWrap<fn(&A, &B, &mut C) -> Z> {
    fn cmp(&self, other: &Self) -> Ordering {
        (self.0 as usize).cmp(&(other.0 as usize))
    }
}

impl<A, B, C, Z> PartialOrd for FnWrap<fn(&A, &B, &mut C) -> Z> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}


impl<A: ?Sized, B, Z> fmt::Debug for FnWrap<fn(&A, &mut B) -> Z> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        (self.0 as *const ()).fmt(f)
    }
}

impl<A: ?Sized, B, Z> Clone for FnWrap<fn(&A, &mut B) -> Z> {
    fn clone(&self) -> Self {
        FnWrap(self.0.clone())
    }
}

impl<A: ?Sized, B, Z> Copy for FnWrap<fn(&A, &mut B) -> Z> {}

impl<A: ?Sized, B, Z> PartialEq for FnWrap<fn(&A, &mut B) -> Z> {
    fn eq(&self, other: &Self) -> bool {
        self.0 as usize == other.0 as usize
    }
}

impl<A: ?Sized, B, Z> Eq for FnWrap<fn(&A, &mut B) -> Z> {}

impl<A: ?Sized, B, Z> Ord for FnWrap<fn(&A, &mut B) -> Z> {
    fn cmp(&self, other: &Self) -> Ordering {
        (self.0 as usize).cmp(&(other.0 as usize))
    }
}

impl<A: ?Sized, B, Z> PartialOrd for FnWrap<fn(&A, &mut B) -> Z> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}
