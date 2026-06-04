/-
  UnifiedAggregation.Trichotomy

  The unification theorem: every aggregation problem falls into at
  least one of the three regimes (Arrow-Debreu, Arrow-Impossibility,
  Schelling-Ising).  Proof is by classical case analysis on the
  existential structure of `Aggregation act F`, with the dichotomy
  helper `aggregation_dichotomy` handling the
  existence-plus-non-uniqueness branch via term-mode
  `Classical.byContradiction`.

  The classical case split on `Nonempty (Aggregation act F)` uses
  `kan_by_cases` (the coproduct-elimination derived tactic over
  `Classical.em`); the existence-plus-non-uniqueness branch is pure
  term mode via `Classical.byContradiction`.  No standard Mathlib
  tactics appear.
-/

import KanTactics
import UnifiedAggregation.Regimes

set_option autoImplicit false

universe u v

namespace UnifiedAggregation

open CompCatTheory

/-- *Aggregation existence dichotomy*: given that at least one
aggregation exists, either all aggregations agree on objects with a
chosen `L` (Arrow-Debreu regime), or two aggregations disagree at some
object (Schelling-Ising regime).  Helper for `trichotomy`. -/
private theorem aggregation_dichotomy
    {Obj : Type u} [Category.{u, u} Obj]
    {G : SymmetryGroup.{u}} {act : GAction G Obj}
    {D : Type v} [Category.{v, v} D]
    {F : ChoiceRule Obj D}
    (h_exists : Nonempty (Aggregation act F)) :
    IsArrowDebreuRegime act F ∨ IsSchellingIsingRegime act F :=
  match h_exists with
  | ⟨L⟩ =>
    (Classical.em
        (∀ L' : Aggregation act F, ∀ Y, L.functor.obj Y = L'.functor.obj Y)).elim
      (fun h_unique => Or.inl ⟨L, h_unique⟩)
      (fun h_unique => Or.inr
        (match (Classical.byContradiction fun h_neg =>
                  h_unique fun L' Y =>
                    Classical.byContradiction fun h_neq => h_neg ⟨L', Y, h_neq⟩
                : ∃ L' : Aggregation act F, ∃ Y,
                    L.functor.obj Y ≠ L'.functor.obj Y) with
          | ⟨L', Y, h_neq⟩ => ⟨L, L', Y, h_neq⟩))

/-- **The unification theorem.**  Every aggregation problem
(`G`-action on a configuration category `Obj`, with a choice rule
`F : Obj ⥤ D`) falls into at least one of three regimes: Arrow-Debreu
(uniquely realized), Arrow-Impossibility (obstructed), or Schelling-
Ising (multi-stable).

Proved by classical case analysis: if no `Aggregation` exists, we
are in Arrow-Impossibility; if one exists, the helper
`aggregation_dichotomy` splits on uniqueness of the objects across
all aggregations.

Concrete witnesses for each regime are constructed in the `Bridge`
modules:
- Arrow-Impossibility: `Bridge.ArrowImpossibility.no_equivariant_constrained_swf`
- Schelling-Ising: `Bridge.SchellingIsing.schelling_ising_z2_degeneracy`
- Arrow-Debreu: `Bridge.ArrowDebreu.arrow_debreu_uniqueness`

Together with this trichotomy, those witnesses establish that the
three classical aggregation results are not independent theorems but
regimes of a single categorical construction. -/
theorem trichotomy
    {Obj : Type u} [Category.{u, u} Obj]
    {G : SymmetryGroup.{u}} (act : GAction G Obj)
    {D : Type v} [Category.{v, v} D]
    (F : ChoiceRule Obj D) :
    IsArrowDebreuRegime act F ∨
    IsArrowImpossibilityRegime act F ∨
    IsSchellingIsingRegime act F := by
  kan_by_cases h_exists : Nonempty (Aggregation act F)
  · -- An aggregation exists ⇒ dichotomy between Arrow-Debreu and Schelling-Ising.
    kan_exact (aggregation_dichotomy h_exists).elim
      (fun h => Or.inl h) (fun h => Or.inr (Or.inr h))
  · -- No aggregation exists ⇒ Arrow-Impossibility.
    kan_exact Or.inr (Or.inl h_exists)

end UnifiedAggregation
