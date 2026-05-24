/-
  UnifiedAggregation.Trichotomy

  The unification theorem: every aggregation problem falls into one
  of the three regimes.  Phase 0 states the conclusion; the proof is
  the long-term deliverable (Phases 1a, 1b, and 2 together).
-/

import UnifiedAggregation.Regimes

set_option autoImplicit false

universe u v

namespace UnifiedAggregation

open CompCatTheory

/-- **The unification theorem.**  Every aggregation problem (G-action on
a configuration category `Obj`, with a choice rule `F : Obj ⥤ D`) falls
into at least one of three regimes: Arrow-Debreu (uniquely realized),
Arrow-Impossibility (obstructed), or Schelling-Ising (multi-stable).

This is the type-level statement of the unification.  The proof is
assembled from:

- Phase 1a: Arrow-Impossibility via `arrow-cat`'s Geanakoplos argument
- Phase 1b: Schelling-Ising via Brock-Durlauf β-family bifurcations
- Phase 2:  Arrow-Debreu via Kakutani fixed-point under convexity

The trichotomy is what makes the three classical results regimes of a
single construction rather than three independent theorems. -/
theorem trichotomy
    {Obj : Type u} [Category.{u, u} Obj]
    {G : SymmetryGroup.{u}} (act : GAction G Obj)
    {D : Type v} [Category.{v, v} D]
    (F : ChoiceRule Obj D) :
    IsArrowDebreuRegime act F ∨
    IsArrowImpossibilityRegime act F ∨
    IsSchellingIsingRegime act F := by
  sorry

end UnifiedAggregation
