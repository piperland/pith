//! Stable semantic identities for Pith.
//!
//! Invariant: semantic entities are addressed by compact copyable ids, never by
//! sprawling GC-owned pointer graphs. Stores own the data; queries pass ids.

macro_rules! id {
    ($name:ident) => {
        #[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
        pub struct $name(pub u32);

        impl $name {
            pub const DUMMY: Self = Self(u32::MAX);
            #[inline]
            #[must_use]
            pub fn index(self) -> usize {
                self.0 as usize
            }
        }
    };
}

id!(FileId);
id!(NodeId);
id!(SymbolId);
id!(TypeId);
id!(SignatureId);
id!(ModuleId);

/// Source span anchored to a file. Byte offsets; half-open [lo, hi).
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct Span {
    pub file: FileId,
    pub lo: u32,
    pub hi: u32,
}

impl Span {
    pub const DUMMY: Self = Self {
        file: FileId::DUMMY,
        lo: 0,
        hi: 0,
    };

    #[inline]
    #[must_use]
    pub fn len(self) -> u32 {
        self.hi.saturating_sub(self.lo)
    }

    #[inline]
    #[must_use]
    pub fn is_empty(self) -> bool {
        self.hi <= self.lo
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn ids_are_copy_and_indexable() {
        let f = FileId(3);
        let n: NodeId = NodeId(f.index() as u32);
        assert_eq!(n.index(), 3);
        assert_ne!(FileId::DUMMY, f);
    }

    #[test]
    fn span_len() {
        let s = Span {
            file: FileId(0),
            lo: 4,
            hi: 10,
        };
        assert_eq!(s.len(), 6);
        assert!(!s.is_empty());
        assert!(Span::DUMMY.is_empty());
    }
}
