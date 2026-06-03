/-
  UnifiedAggregation.FunctorExt

  Extensionality for functors: two functors are equal when their
  `obj` and `map` fields agree.  The `map` field's type depends on
  `obj`, so the natural statement uses `HEq` on the maps.

  comp-cat-theory does not (yet) ship a `Functor.ext` lemma; this
  module fills the gap locally.  It is load-bearing for the group-
  action laws in all three Bridge modules:

  - `Bridge.ArrowImpossibility.profileAction` (uses `Functor.ext`)
  - `Bridge.SchellingIsing.spinConfigAction` (uses
    `Functor.ext_pointwise` for the `(.flip, .flip)` case where
    `act_mul` obj equality requires `SpinConfig.flip_flip`
    pointwise rather than `rfl`)
  - `Bridge.ArrowDebreu.allocationAction` (uses `Functor.ext`)

  Candidate for upstreaming to `comp-cat-theory`; kept local to
  avoid cross-repo churn.
-/

import CompCatTheory.Foundation.Category

set_option autoImplicit false

universe u₁ v₁ u₂ v₂

namespace UnifiedAggregation

open CompCatTheory Category

/-- Extensionality for functors: two functors are equal when their
`obj` and `map` fields agree.  The `map` field's type depends on
`obj`, so the `map`-equality is stated using `HEq`.

After destructuring both functors and using the rfl-patterns on
`h_obj` and `h_map`, the proof fields (`map_id`, `map_comp`) are
propositionally equal by Lean's definitional proof irrelevance, so
the whole structure equality closes by `rfl`. -/
theorem Functor.ext {C : Type u₁} {D : Type u₂}
    [Category.{u₁, v₁} C] [Category.{u₂, v₂} D] : ∀ {F G : C ⥤ D},
    F.obj = G.obj → HEq @F.map @G.map → F = G
  | ⟨_, _, _, _⟩, ⟨_, _, _, _⟩, rfl, HEq.refl _ => rfl

/-- *Pointwise* extensionality for functors: two functors are equal
when their `obj` fields agree pointwise and their `map` fields agree
pointwise (as `HEq`, since `map`'s type depends on `obj`).

This is the load-bearing lemma for proving Functor equalities where
the obj fields are propositionally but not definitionally equal —
the situation that blocks `heq_of_eq` in the simpler `Functor.ext`
recipe.  Uses `subst` to identify obj-fields after `funext`, then
`eq_of_heq` to convert pointwise HEq to pointwise Eq, then `funext`
to lift to function equality.

Proof structure: destructure F and G into their four-tuple form, use
`funext h_obj` to get `F_obj = G_obj` and `subst` to identify them in
the context, use `funext` over `X, Y, f` plus `eq_of_heq` to get
`F_map = G_map`, `subst` again, then `rfl` closes by structure η plus
propositional irrelevance on the residual law fields. -/
theorem Functor.ext_pointwise {C : Type u₁} {D : Type u₂}
    [Category.{u₁, v₁} C] [Category.{u₂, v₂} D]
    (F G : C ⥤ D)
    (h_obj : ∀ X : C, F.obj X = G.obj X)
    (h_map : ∀ {X Y : C} (f : Hom X Y), HEq (F.map f) (G.map f)) :
    F = G := by
  cases F with
  | mk F_obj F_map F_id F_comp =>
  cases G with
  | mk G_obj G_map G_id G_comp =>
    have h_obj_eq : F_obj = G_obj := funext h_obj
    subst h_obj_eq
    have h_map_eq : @F_map = @G_map := by
      funext X Y f
      exact eq_of_heq (h_map f)
    subst h_map_eq
    rfl

end UnifiedAggregation
