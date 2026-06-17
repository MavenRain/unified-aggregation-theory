/-
  UnifiedAggregation.Indiscrete

  The indiscrete (codiscrete / "chaotic") category on a type: exactly
  one morphism between any two objects.  Every morphism is therefore an
  isomorphism and any two objects are isomorphic, yet distinct
  underlying values remain *distinct objects*.

  This is the target category that makes the Schelling-Ising regime
  genuine.  A left Kan extension into a `Discrete` category is unique on
  objects (isomorphic objects are equal there), so symmetry breaking is
  invisible -- this is exactly why the original discrete encoding could
  never witness `IsSchellingIsingRegime` (see
  `UnifiedAggregation.Characterization.lan_obj_unique_discrete`).  Into
  an indiscrete category the universal object is determined only up to
  the canonical isomorphism, so distinct object-representatives are
  genuinely distinct left Kan extensions: the categorical content of a
  spontaneously broken phase.
-/

import CompCatTheory.Foundation.Category
import CompCatTheory.Primitive.KanExtension

set_option autoImplicit false

universe u v w u₁ v₁ u₂ v₂

namespace UnifiedAggregation

open CompCatTheory Category

/-- Carrier for the indiscrete category on `α`.  Wrapped in a structure
(as with `Discrete`) so the `Category` instance attaches without
colliding with other `Category` instances downstream projects might
want on `α` itself. -/
structure Indiscrete (α : Type u) where
  val : α

/-- The indiscrete category on `α`: exactly one morphism (`PUnit`)
between any two objects.  All four category laws hold by `rfl` because
`PUnit` has definitional eta (every element is `PUnit.unit`), so any two
parallel morphisms are definitionally equal. -/
instance indiscreteCategory (α : Type u) : Category.{u, u} (Indiscrete α) where
  Hom _ _ := PUnit
  id _ := PUnit.unit
  comp _ _ := PUnit.unit
  comp_id := fun _ => rfl
  id_comp := fun _ => rfl
  assoc := fun _ _ _ => rfl

/-- Distinct underlying values give distinct *objects* of the indiscrete
category.  Contrast the discrete case: `⟨a⟩` and `⟨b⟩` are isomorphic
here (the unique `PUnit` morphism is an iso) yet unequal, which is the
whole point -- non-uniqueness of a left Kan extension lives at the level
of object equality, not isomorphism. -/
theorem Indiscrete.mk_ne {α : Type u} {a b : α} (h : a ≠ b) :
    (Indiscrete.mk a) ≠ Indiscrete.mk b :=
  fun heq => h (congrArg Indiscrete.val heq)

/-- The constant functor at an object `c` of an indiscrete category.
Object map is constantly `c`; the morphism map is forced into `PUnit`,
so both functor laws hold by `rfl`. -/
def constIndiscrete {C : Type u} [Category.{u, w} C] {α : Type v}
    (c : Indiscrete α) : C ⥤ Indiscrete α where
  obj _ := c
  map _ := PUnit.unit
  map_id _ := rfl
  map_comp _ _ := rfl

/-- **A left Kan extension into an indiscrete target always exists, at
*any* chosen object `c`.**  Realized by the constant functor at `c`,
with unit / descent / factorization / uniqueness all holding by `rfl`
because every hom-set of the target is `PUnit`.

This is the crux of the genuine Schelling-Ising regime: existence is
automatic (so we are not in the Arrow-Impossibility regime), yet the
universal object is pinned only up to the canonical isomorphism, so the
free choice of `c` yields genuinely distinct left Kan extensions whose
object-assignments differ.  Feeding it two distinct phases (the
symmetry-broken `±m_*`) realizes `IsSchellingIsingRegime`. -/
def indiscreteLan {J : Type u₁} {C : Type u₂}
    [Category.{u₁, v₁} J] [Category.{u₂, v₂} C]
    {α : Type v} (K : J ⥤ C) (F : J ⥤ Indiscrete α) (c : Indiscrete α) :
    CompCatTheory.LeftKanExtension K F where
  functor := constIndiscrete c
  unit := { app := fun _ => PUnit.unit, naturality := fun _ => rfl }
  desc := fun _ => { app := fun _ => PUnit.unit, naturality := fun _ => rfl }
  fac := fun _ _ => rfl
  uniq := fun _ _ _ _ => rfl

end UnifiedAggregation
