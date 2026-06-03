/-
  UnifiedAggregation.Regimes

  Three regimes of the aggregation map, each a property of the
  configuration data (Obj + GAction + choice rule):

  - `IsArrowDebreuRegime`: aggregation exists and is object-uniquely
    determined
  - `IsArrowImpossibilityRegime`: no aggregation exists
  - `IsSchellingIsingRegime`: aggregation exists but two
    realizations disagree on some object

  These predicates are the load-bearing form used by
  `UnifiedAggregation.Trichotomy.trichotomy` to prove the joint
  exhaustiveness of the three regimes.  Concrete witnesses are
  constructed in the `Bridge` modules.
-/

import UnifiedAggregation.Aggregation

set_option autoImplicit false

universe u v

namespace UnifiedAggregation

open CompCatTheory

/-- **Arrow-Debreu regime**: the aggregation Kan extension exists
and its underlying functor is uniquely determined up to equality on
objects.

Sufficient condition (classical): the image of `F` in `D` is convex,
so the universal cocone has a unique vertex per orbit.  The symbolic
witness in the framework is
`Bridge.ArrowDebreu.arrow_debreu_uniqueness`. -/
def IsArrowDebreuRegime
    {Obj : Type u} [Category.{u, u} Obj]
    {G : SymmetryGroup.{u}} (act : GAction G Obj)
    {D : Type v} [Category.{v, v} D]
    (F : ChoiceRule Obj D) : Prop :=
  ∃ L : Aggregation act F, ∀ L' : Aggregation act F,
    ∀ Y, L.functor.obj Y = L'.functor.obj Y

/-- **Arrow-Impossibility regime**: no aggregation satisfies the
equivariance, unanimity, and IIA-as-naturality constraints.

The framework witness is
`Bridge.ArrowImpossibility.no_equivariant_constrained_swf`, which
rephrases `arrow-cat`'s `arrow_contrapositive` as the non-existence
of a constraint-satisfying realization of the Kan extension. -/
def IsArrowImpossibilityRegime
    {Obj : Type u} [Category.{u, u} Obj]
    {G : SymmetryGroup.{u}} (act : GAction G Obj)
    {D : Type v} [Category.{v, v} D]
    (F : ChoiceRule Obj D) : Prop :=
  ¬ Nonempty (Aggregation act F)

/-- **Schelling-Ising regime**: the aggregation exists but is
multi-stable, with the universal cocone realized by at least two
non-isomorphic selectors.

The symbolic framework witness is
`Bridge.SchellingIsing.schelling_ising_z2_degeneracy` (distinct
equal-energy configurations at the Int level).  The analytic
witness is `Bridge.SchellingIsing.mean_field_bifurcation` (the
self-consistency equation `m = tanh(β·m)` admits two distinct
real-valued solutions for `β > 1`). -/
def IsSchellingIsingRegime
    {Obj : Type u} [Category.{u, u} Obj]
    {G : SymmetryGroup.{u}} (act : GAction G Obj)
    {D : Type v} [Category.{v, v} D]
    (F : ChoiceRule Obj D) : Prop :=
  ∃ L₁ L₂ : Aggregation act F, ∃ Y,
    L₁.functor.obj Y ≠ L₂.functor.obj Y

end UnifiedAggregation
