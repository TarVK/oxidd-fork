//! Recursive single-threaded apply algorithms

use std::borrow::Borrow;

use oxidd_core::function::BooleanFunction;
use oxidd_core::function::EdgeOfFunc;
use oxidd_core::function::Function;
use oxidd_core::function::TVLFunction;
use oxidd_core::util::AllocResult;
use oxidd_core::util::Borrowed;
use oxidd_core::util::EdgeDropGuard;
use oxidd_core::ApplyCache;
use oxidd_core::Edge;
use oxidd_core::HasApplyCache;
use oxidd_core::HasLevel;
use oxidd_core::InnerNode;
use oxidd_core::Manager;
use oxidd_core::Node;
use oxidd_core::Tag;
use oxidd_derive::Function;
use oxidd_dump::dot::DotStyle;

use super::collect_children;
use super::reduce;
use super::stat;
use super::terminal_bin;
use super::Operation;
use super::QDDOp;
use super::QDDTerminal;

// spell-checker:ignore fnode,gnode,hnode,flevel,glevel,hlevel,ghlevel

/// Recursively apply the 'not' operator to `f`
// pub(super) fn apply_not<M>(manager: &M, f: Borrowed<M::Edge>) -> AllocResult<M::Edge>
// where
//     M: Manager<Terminal = QDDTerminal> + HasApplyCache<M, Operator = QDDOp>,
//     M::InnerNode: HasLevel,
// {
//     stat!(call QDDOp::Not);
//     let node = match manager.get_node(&f) {
//         Node::Inner(node) => node,
//         Node::Terminal(t) => return Ok(manager.get_terminal(!*t.borrow()).unwrap()),
//     };

//     // Query apply cache
//     stat!(cache_query TDDOp::Not);
//     if let Some(h) = manager
//         .apply_cache()
//         .get(manager, QDDOp::Not, &[f.borrowed()])
//     {
//         stat!(cache_hit TDDOp::Not);
//         return Ok(h);
//     }

//     let (f0, f1, f2) = collect_children(node);
//     let level = node.level();

//     let t = EdgeDropGuard::new(manager, apply_not(manager, f0)?);
//     let u = EdgeDropGuard::new(manager, apply_not(manager, f1)?);
//     let e = EdgeDropGuard::new(manager, apply_not(manager, f2)?);
//     let h = reduce(
//         manager,
//         level,
//         t.into_edge(),
//         u.into_edge(),
//         e.into_edge(),
//         QDDOp::Not,
//     )?;

//     // Add to apply cache
//     manager
//         .apply_cache()
//         .add(manager, QDDOp::Not, &[f.borrowed()], h.borrowed());

//     Ok(h)
// }

/// Recursively apply the binary operator `OP` to `f` and `g`
///
/// We use a `const` parameter `OP` to have specialized version of this function
/// for each operator.
pub(super) fn apply_bin<M, const OP: u8>(
    manager: &M,
    f: Borrowed<M::Edge>,
    g: Borrowed<M::Edge>,
) -> AllocResult<M::Edge>
where
    M: Manager<Terminal = QDDTerminal> + HasApplyCache<M, QDDOp>,
    M::InnerNode: HasLevel,
{
    stat!(call OP);
    let (operator, op1, op2) = match terminal_bin::<M, OP>(manager, &f, &g) {
        Operation::Binary(o, op1, op2) => (o, op1, op2),
        Operation::Not(f) => {
            // return apply_not(manager, f);
            return todo!(); // TODO:
        }
        Operation::Done(h) => return Ok(h),
    };

    // Query apply cache
    stat!(cache_query OP);
    if let Some(h) = manager
        .apply_cache()
        .get(manager, operator, &[op1.borrowed(), op2.borrowed()])
    {
        stat!(cache_hit OP);
        return Ok(h);
    }

    let fnode = manager.get_node(&f);
    let gnode = manager.get_node(&g);
    let flevel = fnode.level();
    let glevel = gnode.level();
    let level = std::cmp::min(flevel, glevel);

    // Collect cofactors of all top-most nodes
    let (f, t, b) = if OP == QDDOp::And as u8 {
        // For AND we use the fact that a lot can be factored out, to simplify the construction
        let (f0, f1, f_) = if flevel == level {
            collect_children(fnode.unwrap_inner())
        } else {
            (f.borrowed(), f.borrowed(), f.borrowed())
        };
        let (g0, g1, g_) = if glevel == level {
            collect_children(gnode.unwrap_inner())
        } else {
            (g.borrowed(), g.borrowed(), g.borrowed())
        };

        let f = EdgeDropGuard::new(manager, apply_bin::<M, OP>(manager, f0, g0)?);
        let t = EdgeDropGuard::new(manager, apply_bin::<M, OP>(manager, f1, g1)?);
        let b = EdgeDropGuard::new(manager, apply_bin::<M, OP>(manager, f_, g_)?);
        (f, t, b)
    } else if flevel == glevel {
        let (f0, f1, f_) = collect_children(fnode.unwrap_inner());
        let (g0, g1, g_) = collect_children(gnode.unwrap_inner());

        let f0g0 = EdgeDropGuard::new(
            manager,
            apply_bin::<M, OP>(manager, f0.borrowed(), g0.borrowed())?,
        );
        let f0g_ = EdgeDropGuard::new(manager, apply_bin::<M, OP>(manager, f0, g_.borrowed())?);
        let f_g0 = EdgeDropGuard::new(manager, apply_bin::<M, OP>(manager, f_.borrowed(), g0)?);
        let f = EdgeDropGuard::new(
            manager,
            apply_bin::<M, { QDDOp::And as u8 }>(
                manager,
                f0g0.borrowed(),
                EdgeDropGuard::new(
                    manager,
                    apply_bin::<M, { QDDOp::And as u8 }>(
                        manager,
                        f0g_.borrowed(),
                        f_g0.borrowed(),
                    )?,
                )
                .borrowed(),
            )?,
        );

        let f1g1 = EdgeDropGuard::new(
            manager,
            apply_bin::<M, OP>(manager, f1.borrowed(), g1.borrowed())?,
        );
        let f1g_ = EdgeDropGuard::new(manager, apply_bin::<M, OP>(manager, f1, g_.borrowed())?);
        let f_g1 = EdgeDropGuard::new(manager, apply_bin::<M, OP>(manager, f_.borrowed(), g1)?);
        let t = EdgeDropGuard::new(
            manager,
            apply_bin::<M, { QDDOp::And as u8 }>(
                manager,
                f1g1.borrowed(),
                EdgeDropGuard::new(
                    manager,
                    apply_bin::<M, { QDDOp::And as u8 }>(
                        manager,
                        f1g_.borrowed(),
                        f_g1.borrowed(),
                    )?,
                )
                .borrowed(),
            )?,
        );

        let b = EdgeDropGuard::new(manager, apply_bin::<M, OP>(manager, f_, g_)?);

        (f, t, b)
    } else if flevel < glevel {
        let (f0, f1, f_) = collect_children(fnode.unwrap_inner());

        let f = EdgeDropGuard::new(manager, apply_bin::<M, OP>(manager, f0, g.borrowed())?);
        let t = EdgeDropGuard::new(manager, apply_bin::<M, OP>(manager, f1, g.borrowed())?);
        let b = EdgeDropGuard::new(manager, apply_bin::<M, OP>(manager, f_, g.borrowed())?);
        (f, t, b)
    } else {
        let (g0, g1, g_) = collect_children(gnode.unwrap_inner());

        let f = EdgeDropGuard::new(manager, apply_bin::<M, OP>(manager, f.borrowed(), g0)?);
        let t = EdgeDropGuard::new(manager, apply_bin::<M, OP>(manager, f.borrowed(), g1)?);
        let b = EdgeDropGuard::new(manager, apply_bin::<M, OP>(manager, f.borrowed(), g_)?);
        (f, t, b)
    };

    let h = reduce(
        manager,
        level,
        f.into_edge(),
        t.into_edge(),
        b.into_edge(),
        operator,
    )?;

    // Add to apply cache
    manager
        .apply_cache()
        .add(manager, operator, &[op1, op2], h.borrowed());

    Ok(h)
}
// --- Function Interface ------------------------------------------------------
/// Workaround for https://github.com/rust-lang/rust/issues/49601
trait HasQDDOpApplyCache<M: Manager>: HasApplyCache<M, QDDOp> {}
impl<M: Manager + HasApplyCache<M, QDDOp>> HasQDDOpApplyCache<M> for M {}

/// Three value logic function backed by a ternary decision diagram
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Function, Debug)]
#[repr(transparent)]
pub struct QDDFunction<F: Function>(F);

impl<F: Function> From<F> for QDDFunction<F> {
    #[inline(always)]
    fn from(value: F) -> Self {
        QDDFunction(value)
    }
}

impl<F: Function> QDDFunction<F> {
    /// Convert `self` into the underlying [`Function`]
    #[inline(always)]
    pub fn into_inner(self) -> F {
        self.0
    }
}

impl<F: Function> BooleanFunction for QDDFunction<F>
where
    for<'id> F::Manager<'id>: Manager<Terminal = QDDTerminal> + HasQDDOpApplyCache<F::Manager<'id>>,
    for<'id> <F::Manager<'id> as Manager>::InnerNode: HasLevel,
{
    #[inline]
    fn new_var<'id>(manager: &mut Self::Manager<'id>) -> AllocResult<Self> {
        let f0 = manager.get_terminal(QDDTerminal::False).unwrap();
        let f1 = manager.get_terminal(QDDTerminal::True).unwrap();
        let f_ = manager.get_terminal(QDDTerminal::True).unwrap();
        let edge = manager.add_level(|level| InnerNode::new(level, [f0, f1, f_]))?;
        Ok(Self::from_edge(manager, edge))
    }

    #[inline]
    fn f_edge<'id>(manager: &Self::Manager<'id>) -> EdgeOfFunc<'id, Self> {
        manager.get_terminal(QDDTerminal::False).unwrap()
    }
    #[inline]
    fn t_edge<'id>(manager: &Self::Manager<'id>) -> EdgeOfFunc<'id, Self> {
        manager.get_terminal(QDDTerminal::True).unwrap()
    }

    // #[inline]
    // fn not_edge<'id>(
    //     manager: &Self::Manager<'id>,
    //     edge: &EdgeOfFunc<'id, Self>,
    // ) -> AllocResult<EdgeOfFunc<'id, Self>> {
    //     apply_not(manager, edge.borrowed())
    // }

    #[inline]
    fn and_edge<'id>(
        manager: &Self::Manager<'id>,
        lhs: &EdgeOfFunc<'id, Self>,
        rhs: &EdgeOfFunc<'id, Self>,
    ) -> AllocResult<EdgeOfFunc<'id, Self>> {
        apply_bin::<_, { QDDOp::And as u8 }>(manager, lhs.borrowed(), rhs.borrowed())
    }
    #[inline]
    fn or_edge<'id>(
        manager: &Self::Manager<'id>,
        lhs: &EdgeOfFunc<'id, Self>,
        rhs: &EdgeOfFunc<'id, Self>,
    ) -> AllocResult<EdgeOfFunc<'id, Self>> {
        apply_bin::<_, { QDDOp::Or as u8 }>(manager, lhs.borrowed(), rhs.borrowed())
    }

    fn not_edge<'id>(
        manager: &Self::Manager<'id>,
        edge: &EdgeOfFunc<'id, Self>,
    ) -> AllocResult<EdgeOfFunc<'id, Self>> {
        todo!() // TODO:
    }

    fn nand_edge<'id>(
        manager: &Self::Manager<'id>,
        lhs: &EdgeOfFunc<'id, Self>,
        rhs: &EdgeOfFunc<'id, Self>,
    ) -> AllocResult<EdgeOfFunc<'id, Self>> {
        todo!() // TODO:
    }

    fn nor_edge<'id>(
        manager: &Self::Manager<'id>,
        lhs: &EdgeOfFunc<'id, Self>,
        rhs: &EdgeOfFunc<'id, Self>,
    ) -> AllocResult<EdgeOfFunc<'id, Self>> {
        todo!() // TODO:
    }

    fn xor_edge<'id>(
        manager: &Self::Manager<'id>,
        lhs: &EdgeOfFunc<'id, Self>,
        rhs: &EdgeOfFunc<'id, Self>,
    ) -> AllocResult<EdgeOfFunc<'id, Self>> {
        todo!() // TODO:
    }

    fn equiv_edge<'id>(
        manager: &Self::Manager<'id>,
        lhs: &EdgeOfFunc<'id, Self>,
        rhs: &EdgeOfFunc<'id, Self>,
    ) -> AllocResult<EdgeOfFunc<'id, Self>> {
        todo!() // TODO:
    }

    fn imp_edge<'id>(
        manager: &Self::Manager<'id>,
        lhs: &EdgeOfFunc<'id, Self>,
        rhs: &EdgeOfFunc<'id, Self>,
    ) -> AllocResult<EdgeOfFunc<'id, Self>> {
        todo!() // TODO:
    }

    fn imp_strict_edge<'id>(
        manager: &Self::Manager<'id>,
        lhs: &EdgeOfFunc<'id, Self>,
        rhs: &EdgeOfFunc<'id, Self>,
    ) -> AllocResult<EdgeOfFunc<'id, Self>> {
        todo!() // TODO:
    }

    fn sat_count_edge<'id, N: oxidd_core::util::SatCountNumber, S: std::hash::BuildHasher>(
        manager: &Self::Manager<'id>,
        edge: &EdgeOfFunc<'id, Self>,
        vars: oxidd_core::LevelNo,
        cache: &mut oxidd_core::util::SatCountCache<N, S>,
    ) -> N {
        todo!() // TODO:
    }

    fn pick_cube_edge<'id, 'a, I>(
        manager: &'a Self::Manager<'id>,
        edge: &'a EdgeOfFunc<'id, Self>,
        order: impl IntoIterator<IntoIter = I>,
        choice: impl FnMut(&Self::Manager<'id>, &EdgeOfFunc<'id, Self>) -> bool,
    ) -> Option<Vec<oxidd_core::util::OptBool>>
    where
        I: ExactSizeIterator<Item = &'a EdgeOfFunc<'id, Self>>,
    {
        todo!() // TODO:
    }

    fn eval_edge<'id, 'a>(
        manager: &'a Self::Manager<'id>,
        edge: &'a EdgeOfFunc<'id, Self>,
        args: impl IntoIterator<Item = (Borrowed<'a, EdgeOfFunc<'id, Self>>, bool)>,
    ) -> bool {
        todo!() // TODO:
    }
}

impl<F: Function, T: Tag> DotStyle<T> for QDDFunction<F> {
    fn edge_style(
        no: usize,
        _tag: T,
    ) -> (oxidd_dump::dot::EdgeStyle, bool, oxidd_dump::dot::Color) {
        (
            if no == 0 {
                oxidd_dump::dot::EdgeStyle::Solid
            } else if no == 1 {
                oxidd_dump::dot::EdgeStyle::Dotted
            } else {
                oxidd_dump::dot::EdgeStyle::Dashed
            },
            false,
            oxidd_dump::dot::Color::BLACK,
        )
    }
}
