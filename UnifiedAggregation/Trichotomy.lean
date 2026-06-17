/-
  UnifiedAggregation.Trichotomy

  The exhaustiveness half of the unification: every aggregation problem
  falls into at least one of the three regimes (Arrow-Debreu,
  Arrow-Impossibility, Schelling-Ising).  Proof is by classical case
  analysis on the existential structure of `Aggregation act F`, with the
  dichotomy helper `aggregation_dichotomy` handling the
  existence-plus-non-uniqueness branch via term-mode
  `Classical.byContradiction`.

  This theorem only establishes that the regimes are jointly exhaustive.
  That each regime is genuinely *inhabited* by a classical aggregation
  phenomenon -- and that all three are instances of the one `Aggregation`
  (left Kan extension along the orbit projection) construction -- is the
  separate, load-bearing content proved in
  `UnifiedAggregation.TrichotomyWitnesses`.

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

/-- **The trichotomy (exhaustiveness half).**  Every aggregation problem
(`G`-action on a configuration category `Obj`, with a choice rule
`F : Obj ⥤ D`) falls into at least one of three regimes: Arrow-Debreu
(uniquely realized), Arrow-Impossibility (obstructed), or Schelling-
Ising (multi-stable).

Proved by classical case analysis: if no `Aggregation` exists, we
are in Arrow-Impossibility; if one exists, the helper
`aggregation_dichotomy` splits on object-uniqueness across all
aggregations.

This is the *exhaustiveness* half of the unification: the three regimes
cover every problem.  On its own it is a classical case split and says
nothing about the three classical results -- a regime is only meaningful
once it is shown to be *inhabited* by an actual aggregation phenomenon
realized through this same `Aggregation` construction.  That
*inhabitation* half is `TrichotomyWitnesses.trichotomy_regimes_realized`,
assembled from the genuine regime witnesses:
- Arrow-Impossibility: `Bridge.ArrowImpossibility.arrow_impossibility_regime`
  (a Pareto+IIA social welfare function has *no* left Kan extension, by
  Arrow's theorem via `Characterization.lan_implies_orbit_constant`).
- Arrow-Debreu: `Bridge.SchellingIsing.paramagnetic_arrow_debreu_regime`
  (`β ≤ 1`: a unique phase, so the aggregation is object-unique).
- Schelling-Ising: `Bridge.SchellingIsing.schelling_ising_regime`
  (`β > 1`: the symmetry-broken pair `±m_*`, so the aggregation is
  object-non-unique).

The discrete-target obstruction
`Characterization.not_schelling_ising_discrete` records why the
Schelling-Ising witness must use the indiscrete *phase* target rather
than the discrete encoding the other regimes use. -/
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
