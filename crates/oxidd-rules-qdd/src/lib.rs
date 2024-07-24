//! Rules and other basic definitions for general ternary decision diagrams
//!
//! ## Feature flags
#![doc = document_features::document_features!()]
#![forbid(unsafe_code)]
// `'id` lifetimes may make the code easier to understand
#![allow(clippy::needless_lifetimes)]

use std::borrow::Borrow;
use std::fmt;
use std::hash::Hash;

use oxidd_core::util::AllocResult;
use oxidd_core::util::Borrowed;
use oxidd_core::DiagramRules;
use oxidd_core::Edge;
use oxidd_core::HasApplyCache;
use oxidd_core::InnerNode;
use oxidd_core::LevelNo;
use oxidd_core::Manager;
use oxidd_core::Node;
use oxidd_core::ReducedOrNew;
use oxidd_derive::Countable;
use oxidd_dump::dddmp::AsciiDisplay;

//#[cfg(feature = "multi-threading")]
//mod apply_rec_mt;
mod apply_rec_st;

// --- Reduction Rules ---------------------------------------------------------

/// [`DiagramRules`] for ternary decision diagrams
pub struct QDDRules;

impl<E: Edge, N: InnerNode<E>> DiagramRules<E, N, QDDTerminal> for QDDRules {
    type Cofactors<'a> = N::ChildrenIter<'a> where N: 'a, E: 'a;

    #[inline]
    #[must_use]
    fn reduce<M: Manager<Edge = E, InnerNode = N, Terminal = QDDTerminal>>(
        manager: &M,
        level: LevelNo,
        children: impl IntoIterator<Item = E>,
    ) -> ReducedOrNew<E, N> {
        let mut it = children.into_iter();
        let t = it.next().unwrap();
        let u = it.next().unwrap();
        let e = it.next().unwrap();
        debug_assert!(it.next().is_none());

        if t == u && u == e {
            manager.drop_edge(u);
            manager.drop_edge(e);
            ReducedOrNew::Reduced(t)
        } else {
            ReducedOrNew::New(N::new(level, [t, u, e]), Default::default())
        }
    }

    #[inline]
    #[must_use]
    fn cofactors(_tag: E::Tag, node: &N) -> Self::Cofactors<'_> {
        node.children()
    }
}

#[inline(always)]
fn reduce<M>(
    manager: &M,
    level: LevelNo,
    t: M::Edge,
    u: M::Edge,
    e: M::Edge,
    op: QDDOp,
) -> AllocResult<M::Edge>
where
    M: Manager<Terminal = QDDTerminal>,
{
    let _ = op;
    let tmp = <QDDRules as DiagramRules<_, _, _>>::reduce(manager, level, [t, u, e]);
    if let ReducedOrNew::Reduced(..) = &tmp {
        stat!(reduced op);
    }
    tmp.then_insert(manager, level)
}

// --- Terminal Type -----------------------------------------------------------

/// Terminal nodes in quasi decision diagrams
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Countable, Debug)]
#[repr(u8)]
#[allow(missing_docs)]
pub enum QDDTerminal {
    False,
    True,
}

impl std::ops::Not for QDDTerminal {
    type Output = QDDTerminal;

    fn not(self) -> Self::Output {
        match self {
            QDDTerminal::False => QDDTerminal::True,
            QDDTerminal::True => QDDTerminal::False,
        }
    }
}

/// Error returned when parsing a [`QDDTerminal`] from string fails
#[derive(Debug, PartialEq, Eq)]
pub struct ParseTerminalErr;

impl std::str::FromStr for QDDTerminal {
    type Err = ParseTerminalErr;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "f" | "F" | "false" | "False" | "FALSE" | "⊥" => Ok(QDDTerminal::False),
            "t" | "T" | "true" | "True" | "TRUE" | "⊤" => Ok(QDDTerminal::True),
            _ => Err(ParseTerminalErr),
        }
    }
}

impl AsciiDisplay for QDDTerminal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        match self {
            QDDTerminal::False => f.write_str("F"),
            QDDTerminal::True => f.write_str("T"),
        }
    }
}

impl fmt::Display for QDDTerminal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            QDDTerminal::False => f.write_str("⊥"),
            QDDTerminal::True => f.write_str("⊤"),
        }
    }
}

// --- Operations & Apply Implementation ---------------------------------------

/// Native operations of this QDD implementation
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
#[repr(u8)]
#[allow(missing_docs)]
pub enum QDDOp {
    // Not,
    And,
    Or,
    // Nand,
    // Nor,
    // Xor,
    // Equiv,
    // Imp,
    // ImpStrict,

    // /// If-then-else
    // Ite,
}

/// Collect the two children of a ternary node
#[inline]
#[must_use]
fn collect_children<E: Edge, N: InnerNode<E>>(
    node: &N,
) -> (
    // False
    Borrowed<E>,
    // True
    Borrowed<E>,
    // Both
    Borrowed<E>,
) {
    debug_assert_eq!(N::ARITY, 3);
    let mut it = node.children();
    let f = it.next().unwrap();
    let t = it.next().unwrap();
    let b = it.next().unwrap();
    debug_assert!(it.next().is_none());
    (f, t, b)
}

enum Operation<'a, E: 'a + Edge> {
    Binary(QDDOp, Borrowed<'a, E>, Borrowed<'a, E>),
    Not(Borrowed<'a, E>),
    Done(E),
}

/// Terminal case for binary operators
#[inline]
fn terminal_bin<'a, M: Manager<Terminal = QDDTerminal>, const OP: u8>(
    m: &M,
    f: &'a M::Edge,
    g: &'a M::Edge,
) -> Operation<'a, M::Edge> {
    use Node::*;
    use Operation::*;
    use QDDTerminal::*;

    if OP == QDDOp::And as u8 {
        if f == g {
            return Done(m.clone_edge(f));
        }
        match (m.get_node(f), m.get_node(g)) {
            (Terminal(t), _) | (_, Terminal(t)) if *t.borrow() == False => {
                Done(m.get_terminal(False).unwrap())
            }
            (Terminal(t), _) if *t.borrow() == True => Done(m.clone_edge(g)),
            (_, Terminal(t)) if *t.borrow() == True => Done(m.clone_edge(f)),
            // Both terminal U is handled above
            // One terminal U or both inner
            _ if f > g => Binary(QDDOp::And, g.borrowed(), f.borrowed()),
            _ => Binary(QDDOp::And, f.borrowed(), g.borrowed()),
        }
    } else if OP == QDDOp::Or as u8 {
        if f == g {
            return Done(m.clone_edge(f));
        }
        match (m.get_node(f), m.get_node(g)) {
            (Terminal(t), _) | (_, Terminal(t)) if *t.borrow() == True => {
                Done(m.get_terminal(True).unwrap())
            }
            (Terminal(t), _) if *t.borrow() == False => Done(m.clone_edge(g)),
            (_, Terminal(t)) if *t.borrow() == False => Done(m.clone_edge(f)),
            _ if f > g => Binary(QDDOp::Or, g.borrowed(), f.borrowed()),
            _ => Binary(QDDOp::Or, f.borrowed(), g.borrowed()),
        }
    } else {
        unreachable!("invalid binary operator")
    }
}

// --- Function Interface ------------------------------------------------------

/// Workaround for https://github.com/rust-lang/rust/issues/49601
// trait HasQDDOpApplyCache<M: Manager>: HasApplyCache<M, Operator = QDDOp> {}
// impl<M: Manager + HasApplyCache<M, Operator = QDDOp>> HasQDDOpApplyCache<M> for M {}

//#[cfg(feature = "multi-threading")]
//pub use apply_rec_mt::TDDFunctionMT;
pub use apply_rec_st::QDDFunction;

// use oxidd;
// oxidd::util::manager_data!(QDDManager for QDD, operator: QDDOp, cache_max_arity: 3);

// oxidd::util::manager_ref_index_based!(pub struct QDDManagerRef(<QDD as DD>::ManagerRef) with QDDManagerData);

// --- Statistics --------------------------------------------------------------

#[cfg(feature = "statistics")]
struct StatCounters {
    calls: std::sync::atomic::AtomicI64,
    cache_queries: std::sync::atomic::AtomicI64,
    cache_hits: std::sync::atomic::AtomicI64,
    reduced: std::sync::atomic::AtomicI64,
}

#[cfg(feature = "statistics")]
impl StatCounters {
    const INIT: StatCounters = StatCounters {
        calls: std::sync::atomic::AtomicI64::new(0),
        cache_queries: std::sync::atomic::AtomicI64::new(0),
        cache_hits: std::sync::atomic::AtomicI64::new(0),
        reduced: std::sync::atomic::AtomicI64::new(0),
    };

    fn print(counters: &[Self], labels: &[&str]) {
        // spell-checker:ignore ctrs
        for (ctrs, op) in counters.iter().zip(labels) {
            let calls = ctrs.calls.swap(0, std::sync::atomic::Ordering::Relaxed);
            let cache_queries = ctrs
                .cache_queries
                .swap(0, std::sync::atomic::Ordering::Relaxed);
            let cache_hits = ctrs
                .cache_hits
                .swap(0, std::sync::atomic::Ordering::Relaxed);
            let reduced = ctrs.reduced.swap(0, std::sync::atomic::Ordering::Relaxed);

            if calls == 0 {
                continue;
            }

            let terminal_percent = (calls - cache_queries) as f32 / calls as f32 * 100.0;
            let cache_hit_percent = cache_hits as f32 / cache_queries as f32 * 100.0;
            eprintln!("  {op}: calls: {calls}, cache queries: {cache_queries} ({terminal_percent} % terminal cases), cache hits: {cache_hits} ({cache_hit_percent} %), reduced: {reduced}");
        }
    }
}

#[cfg(feature = "statistics")]
static STAT_COUNTERS: [crate::StatCounters; 10] = [crate::StatCounters::INIT; 10];

#[cfg(feature = "statistics")]
/// Print statistics to stderr
pub fn print_stats() {
    eprintln!("[oxidd_rules_qdd]");
    // FIXME: we should auto generate the labels
    crate::StatCounters::print(
        &STAT_COUNTERS,
        &[
            "Not",
            "And",
            "Or",
            "Nand",
            "Nor",
            "Xor",
            "Equiv",
            "Imp",
            "ImpStrict",
            "Ite",
        ],
    );
}

#[cfg(not(feature = "statistics"))]
macro_rules! stat {
    (call $op:expr) => {};
    (cache_query $op:expr) => {};
    (cache_hit $op:expr) => {};
    (reduced $op:expr) => {};
}

#[cfg(feature = "statistics")]
macro_rules! stat {
    (call $op:expr) => {
        STAT_COUNTERS[$op as usize]
            .calls
            .fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    };
    (cache_query $op:expr) => {
        STAT_COUNTERS[$op as usize]
            .cache_queries
            .fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    };
    (cache_hit $op:expr) => {
        STAT_COUNTERS[$op as usize]
            .cache_hits
            .fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    };
    (reduced $op:expr) => {
        STAT_COUNTERS[$op as usize]
            .reduced
            .fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    };
}

pub(crate) use stat;
