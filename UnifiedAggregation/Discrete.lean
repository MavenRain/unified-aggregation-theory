/-
  UnifiedAggregation.Discrete

  Discrete category construction.  Given a type `α`, builds a category
  `Discrete α` whose objects are values of `α` and whose only morphisms
  are identities.

  Used by `Bridge.ArrowImpossibility` to view `Profile m α` and
  `StrictPref α` as categorical objects: both carry no natural morphism
  structure for the social-choice problem, only object-level data
  matters.

  Could plausibly upstream to `comp-cat-theory`; kept here for now to
  avoid cross-repo work during Phase 1.
-/

import CompCatTheory.Foundation.Category

set_option autoImplicit false

universe u v

namespace UnifiedAggregation

open CompCatTheory

/-- The carrier type for the discrete category on `α`.  Wrapped in a
structure (rather than a `def := α`) so the `Category` instance below
attaches without colliding with other `Category` instances downstream
projects might want on `α` itself. -/
structure Discrete (α : Type u) where
  val : α

/-- A morphism in the discrete category on `α`: a single constructor
witnessing object equality.  `DiscreteHom X Y` is empty unless `X = Y`,
in which case it has a unique inhabitant.

Inductive rather than `PLift (X = Y)` so the category laws (`comp_id`,
`id_comp`, `assoc`) reduce by case analysis on the constructor without
needing `PLift` η-expansion. -/
inductive DiscreteHom {α : Type u} : Discrete α → Discrete α → Type u
  | id : (X : Discrete α) → DiscreteHom X X

/-- Composition of discrete morphisms.  Only the identity-identity
case arises because `DiscreteHom X Y` is inhabited only when `X = Y`. -/
def DiscreteHom.comp {α : Type u} {X Y Z : Discrete α}
    (f : DiscreteHom X Y) (g : DiscreteHom Y Z) : DiscreteHom X Z :=
  match f, g with
  | .id _, .id _ => .id _

/-- The discrete category on `α`: objects are values of `α`, morphisms
are identities only, all four category laws hold definitionally on the
single-constructor case. -/
instance discreteCategory (α : Type u) : Category.{u, u} (Discrete α) where
  Hom X Y := DiscreteHom X Y
  id X := DiscreteHom.id X
  comp f g := f.comp g
  comp_id := fun f => match f with | .id _ => rfl
  id_comp := fun f => match f with | .id _ => rfl
  assoc := fun f g h => match f, g, h with | .id _, .id _, .id _ => rfl

/-- Functorial lift of a function `α → β` to a functor
`Discrete α ⥤ Discrete β`.  Discrete categories make any function a
functor: object-level mapping by `φ`, morphism-level mapping by the
identity (the only morphism available). -/
def discreteFunctor {α : Type u} {β : Type v} (φ : α → β) :
    Discrete α ⥤ Discrete β where
  obj X := ⟨φ X.val⟩
  map h := match h with | .id _ => DiscreteHom.id _
  map_id _ := rfl
  map_comp f g := match f, g with | .id _, .id _ => rfl

end UnifiedAggregation
