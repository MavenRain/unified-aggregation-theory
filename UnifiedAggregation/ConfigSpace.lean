/-
  UnifiedAggregation.ConfigSpace

  The "input data" side of the unification: a small category of
  micro-configurations together with a symmetry group acting on it.

  No Mathlib dependency.  `SymmetryGroup` is defined directly so the
  framework stays portable across the categorical, social-choice, and
  statistical-mechanics layers.
-/

import CompCatTheory.Foundation.Category

set_option autoImplicit false

universe u v

namespace UnifiedAggregation

open CompCatTheory Functor

/-- A *symmetry group*: a type with identity, multiplication, and
inverse satisfying the four group laws.  Written categorically (no
Mathlib `Group` typeclass) so the unification remains self-contained. -/
structure SymmetryGroup where
  carrier   : Type u
  one       : carrier
  mul       : carrier → carrier → carrier
  inv       : carrier → carrier
  one_mul   : ∀ g, mul one g = g
  mul_one   : ∀ g, mul g one = g
  mul_assoc : ∀ g h k, mul (mul g h) k = mul g (mul h k)
  mul_inv   : ∀ g, mul g (inv g) = one
  inv_mul   : ∀ g, mul (inv g) g = one

/-- A *G-action* on a small category C: a homomorphism from the group G
into the endofunctor category on C.  For each group element g we get an
endofunctor `act g : C ⥤ C`, with `act_one` and `act_mul` enforcing the
group-homomorphism laws.

The convention `act (g · h) = act h ⋙ act g` is the standard left action
in our composition order (`F ⋙ G` means "apply F first, then G"). -/
structure GAction (G : SymmetryGroup.{u}) (Obj : Type v)
    [Category.{v, v} Obj] where
  act     : G.carrier → (Obj ⥤ Obj)
  act_one : act G.one = Functor.idFunctor Obj
  act_mul : ∀ g h, act (G.mul g h) = act h ⋙ act g

end UnifiedAggregation
