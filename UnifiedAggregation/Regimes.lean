/-
  UnifiedAggregation.Regimes

  Three regimes of the aggregation map, each a property of the
  configuration data (Obj + GAction + choice rule).

  - `IsArrowDebreuRegime`: aggregation exists uniquely
  - `IsArrowImpossibilityRegime`: aggregation is obstructed
  - `IsSchellingIsingRegime`: aggregation exists but is multi-stable

  Phase 0: predicate signatures only.  The bodies below capture the
  *shape* of each claim and are placeholders for the Phase 1+ formal
  content; the equivariance / unanimity / IIA-naturality constraints
  that turn these into the genuine regime predicates are layered in
  during Phase 1a.
-/

import UnifiedAggregation.Aggregation

set_option autoImplicit false

universe u v

namespace UnifiedAggregation

open CompCatTheory

/-- **Arrow-Debreu regime**: the aggregation Kan extension exists and
its underlying functor is uniquely determined up to the natural notion
of equality on objects.

Sufficient condition (classical): the image of F in D is convex, so
the universal cocone has a unique vertex per orbit.  Phase 2 deliverable. -/
def IsArrowDebreuRegime
    {Obj : Type u} [Category.{u, u} Obj]
    {G : SymmetryGroup.{u}} (act : GAction G Obj)
    {D : Type v} [Category.{v, v} D]
    (F : ChoiceRule Obj D) : Prop :=
  ∃ L : Aggregation act F, ∀ L' : Aggregation act F,
    ∀ Y, L.functor.obj Y = L'.functor.obj Y

/-- **Arrow-Impossibility regime**: no aggregation satisfies the
equivariance, unanimity, and IIA-as-naturality constraints.

Phase 1a deliverable: this is what `arrow-cat` already proves on the
social-choice side.  The Phase 1a bridge rephrases arrow-cat's
`arrow_contrapositive` as the non-existence of a constraint-satisfying
realization of the Kan extension in this framework. -/
def IsArrowImpossibilityRegime
    {Obj : Type u} [Category.{u, u} Obj]
    {G : SymmetryGroup.{u}} (act : GAction G Obj)
    {D : Type v} [Category.{v, v} D]
    (F : ChoiceRule Obj D) : Prop :=
  ¬ Nonempty (Aggregation act F)

/-- **Schelling-Ising regime**: the aggregation exists but is multi-
stable, with the universal cocone realized by at least two non-
isomorphic selectors.

Phase 1b deliverable: the mean-field Z_2 case, where the number of
connected components of the selector space bifurcates with the inverse-
temperature β at a critical β_c. -/
def IsSchellingIsingRegime
    {Obj : Type u} [Category.{u, u} Obj]
    {G : SymmetryGroup.{u}} (act : GAction G Obj)
    {D : Type v} [Category.{v, v} D]
    (F : ChoiceRule Obj D) : Prop :=
  ∃ L₁ L₂ : Aggregation act F, ∃ Y,
    L₁.functor.obj Y ≠ L₂.functor.obj Y

end UnifiedAggregation
