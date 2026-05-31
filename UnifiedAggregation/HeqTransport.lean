import Lean

/-!
# UnifiedAggregation.HeqTransport

Tactics for manipulating `HEq` goals through outer-layer casts.

## Motivation

The orbit-groupoid construction (`OrbitHom`, `orbitGroupoidCategory`,
`orbitProjection` in `UnifiedAggregation.Aggregation`) produces
goals of the form

    HEq (h₁ ▸ (f ≫ g))
        (h₂ ▸ ((h₃ ▸ f) ≫ F.map (h₄ ▸ g)))

where `h₁, …, h₄` are functor equalities induced by the `act_one`
and `act_mul` laws of a group action.  Closing these requires
peeling the casts at the outer layers so the underlying
morphism-level equality can be inspected.

## Tactics

- `heq_refl` closes `HEq a a` (reflexive case).
- `heq_lhs_uncast` / `heq_rhs_uncast` strip one outer `Eq.recOn`
  cast (specialised non-dependent-motive form).
- `heq_lhs_uncast_cast` / `heq_rhs_uncast_cast` strip one outer
  `cast` (non-dependent type-level conversion).
- `heq_lhs_uncast_dep` / `heq_rhs_uncast_dep` strip one outer
  `Eq.rec` whose motive lambda binds the equation argument (the
  form `▸` produces when rewriting under a type-level application
  such as `Functor.obj`).
- `heq_strip` iterates all six over both sides, then tries refl.

## Scope

These tactics handle the *outer* layer of casts on each side.
They do not recurse into structural subterms (composition, functor
application).  Goals where the casts are nested inside `≫` or
`Functor.map` need additional HEq-congruence machinery.

This module deliberately lives in `unified-aggregation-theory`
rather than `kan-tactics`: kan-tactics is the minimal spanning
set of tactics derived from Kan extension primitives, and HEq
cast machinery does not reduce to any of those.
-/


namespace UnifiedAggregation

open Lean Meta Elab Tactic

set_option autoImplicit false

universe u v

/-- Helper for stripping an `Eq.rec` cast under a dependent motive.
Takes the equation explicitly so motive inference proceeds from the
goal rather than from `Init.eqRec_heq_iff`'s fully-implicit
signature (which Lean cannot disambiguate without explicit motive
hints in tactic context). -/
theorem eqRec_heq_dep {α : Sort u} {a b : α} (h : a = b)
    {motive : (x : α) → a = x → Sort v}
    (refl : motive a (Eq.refl a)) :
    HEq (@Eq.rec α a motive refl b h) refl := by
  cases h
  exact HEq.refl _

/-- Close an `HEq` goal `HEq a a` (both sides definitionally
equal). -/
syntax "heq_refl" : tactic
macro_rules
  | `(tactic| heq_refl) => `(tactic| exact HEq.refl _)

/-- Strip one outer `Eq.recOn` cast from the LHS of an HEq goal.
Transforms `HEq (h ▸ x) y` into `HEq x y` via `eqRec_heq`. -/
syntax "heq_lhs_uncast" : tactic
macro_rules
  | `(tactic| heq_lhs_uncast) =>
    `(tactic| refine HEq.trans (eqRec_heq _ _) ?_)

/-- Strip one outer `Eq.recOn` cast from the RHS of an HEq goal. -/
syntax "heq_rhs_uncast" : tactic
macro_rules
  | `(tactic| heq_rhs_uncast) =>
    `(tactic| refine HEq.trans ?_ (HEq.symm (eqRec_heq _ _)))

/-- Strip one outer `cast` from the LHS of an HEq goal.  Variant
of `heq_lhs_uncast` using `cast_heq` for the non-dependent
type-conversion form of `▸`. -/
syntax "heq_lhs_uncast_cast" : tactic
macro_rules
  | `(tactic| heq_lhs_uncast_cast) =>
    `(tactic| refine HEq.trans (cast_heq _ _) ?_)

/-- Strip one outer `cast` from the RHS of an HEq goal. -/
syntax "heq_rhs_uncast_cast" : tactic
macro_rules
  | `(tactic| heq_rhs_uncast_cast) =>
    `(tactic| refine HEq.trans ?_ (HEq.symm (cast_heq _ _)))

/-- Strip one outer `Eq.rec` cast from the LHS of an HEq goal,
handling the *dependent-motive* form produced by `▸` when the
motive lambda binds the equation argument (e.g.  when rewriting
under `Functor.obj`).  Uses the local helper `eqRec_heq_dep` with
the equation as an explicit argument so motive inference succeeds. -/
syntax "heq_lhs_uncast_dep" : tactic
macro_rules
  | `(tactic| heq_lhs_uncast_dep) =>
    `(tactic| refine HEq.trans (UnifiedAggregation.eqRec_heq_dep _ _) ?_)

/-- Strip one outer `Eq.rec` cast from the RHS of an HEq goal,
handling the dependent-motive form. -/
syntax "heq_rhs_uncast_dep" : tactic
macro_rules
  | `(tactic| heq_rhs_uncast_dep) =>
    `(tactic| refine HEq.trans ?_ (HEq.symm (UnifiedAggregation.eqRec_heq_dep _ _)))

/-- Iteratively strip outer casts from both sides of an HEq goal,
then close with `HEq.refl` if both sides have aligned.

Algorithm:
1. Try LHS uncast via `eqRec_heq`, then `cast_heq`, then
   `eqRec_heq_dep` (dependent-motive form).
2. Try the same three on RHS.
3. Loop if any step made progress.
4. After convergence, attempt `HEq.refl _` to close. -/
syntax "heq_strip" : tactic
elab_rules : tactic
  | `(tactic| heq_strip) => do
    let tryTac (stx : Syntax) : TacticM Bool := do
      try
        evalTactic stx
        pure true
      catch _ =>
        pure false
    let lhsTac <- `(tactic| refine HEq.trans (eqRec_heq _ _) ?_)
    let rhsTac <- `(tactic| refine HEq.trans ?_ (HEq.symm (eqRec_heq _ _)))
    let lhsCastTac <- `(tactic| refine HEq.trans (cast_heq _ _) ?_)
    let rhsCastTac <- `(tactic| refine HEq.trans ?_ (HEq.symm (cast_heq _ _)))
    let lhsDepTac <- `(tactic|
      refine HEq.trans (UnifiedAggregation.eqRec_heq_dep _ _) ?_)
    let rhsDepTac <- `(tactic|
      refine HEq.trans ?_ (HEq.symm (UnifiedAggregation.eqRec_heq_dep _ _)))
    let reflTac <- `(tactic| exact HEq.refl _)
    let rec loop (fuel : Nat) : TacticM Unit := do
      match fuel with
      | 0 => pure ()
      | fuel' + 1 =>
        let p₁ <- tryTac lhsTac
        let p₂ <- tryTac rhsTac
        let p₃ <- tryTac lhsCastTac
        let p₄ <- tryTac rhsCastTac
        let p₅ <- tryTac lhsDepTac
        let p₆ <- tryTac rhsDepTac
        if p₁ || p₂ || p₃ || p₄ || p₅ || p₆ then loop fuel' else pure ()
    loop 64
    let _ <- tryTac reflTac
    pure ()

/-! ## Smoke tests

Inline `private example` blocks exercising each tactic on the
canonical patterns the orbit-groupoid HEqs are built from. -/

private example {α : Type u} (a : α) : HEq a a := by heq_refl

private example {α : Sort u} {motive : α → Sort v} {a b : α}
    (h : a = b) (x : motive a) : HEq (h ▸ x) x := by heq_strip

private example {α : Sort u} {motive : α → Sort v} {a b : α}
    (h : a = b) (x : motive a) : HEq x (h ▸ x) := by heq_strip

private example {α : Sort u} {motive : α → Sort v} {a b c : α}
    (h₁ : a = b) (h₂ : a = c) (x : motive a) :
    HEq (h₁ ▸ x) (h₂ ▸ x) := by heq_strip

private example {α : Sort u} {motive : α → Sort v} {a b c : α}
    (h₁ : a = b) (h₂ : b = c) (x : motive a) :
    HEq (h₂ ▸ h₁ ▸ x) x := by heq_strip

private example {α β : Sort u} (h : α = β) (a : α) :
    HEq (cast h a) a := by heq_strip

private example {α β : Sort u} (h : α = β) (a : α) :
    HEq a (cast h a) := by heq_strip

private example {α : Sort u} {a b : α} (h : a = b)
    (motive : (x : α) → a = x → Sort v)
    (refl : motive a (Eq.refl a)) :
    HEq (@Eq.rec α a motive refl b h) refl := by heq_strip

private example {α : Sort u} {a b : α} (h : a = b)
    (motive : (x : α) → a = x → Sort v)
    (refl : motive a (Eq.refl a)) :
    HEq refl (@Eq.rec α a motive refl b h) := by heq_strip

end UnifiedAggregation
