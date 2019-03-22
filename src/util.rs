use nom::types::CompleteStr;
use nom_locate::LocatedSpan;

type Span<'a> = LocatedSpan<CompleteStr<'a>>;

#[derive(PartialEq, Eq, Debug, Clone, Hash, PartialOrd, Ord)]
pub struct SrcLocation {
    offset: usize,
    line: u32,
    col: usize,
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
