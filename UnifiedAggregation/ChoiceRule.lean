/-
  UnifiedAggregation.ChoiceRule

  A *choice rule* is a functor C ⥤ D from the configuration category
  into a category of macro-outcomes (prices, social orderings, phases).
  The β-parameterized variant is the Brock-Durlauf logit family indexed
  by inverse temperature.
-/

import UnifiedAggregation.ConfigSpace

set_option autoImplicit false

universe u v w

namespace UnifiedAggregation

open CompCatTheory

/-- A *choice rule* is a functor from the configuration category to the
outcome category.  This is the local-to-local map the aggregation
mechanism will lift along the orbit projection. -/
abbrev ChoiceRule (Obj : Type u) (D : Type v)
    [Category.{u, u} Obj] [Category.{v, v} D] :=
  Obj ⥤ D

/-- A *β-family of choice rules*: a function from a parameter type β
into choice rules.  This indexes the Brock-Durlauf statistical-
mechanics-of-discrete-choice family: each β picks out a softmax/logit
choice rule of inverse temperature β, with β → ∞ recovering pure
best-response and β → 0 giving uniform randomization.

The ℝ-valued parameter is left abstract so the framework stays neutral
about which real-number representation downstream consumers use (Lean's
`Real`, `NNReal`, `EReal`, a dyadic-rationals stand-in, etc.). -/
structure BetaChoiceFamily
    (β : Type w)
    (Obj : Type u) (D : Type v)
    [Category.{u, u} Obj] [Category.{v, v} D] where
  rule : β → ChoiceRule Obj D

end UnifiedAggregation
