/-
  UnifiedAggregation.FunctorExt

  Extensionality for functors: two functors are equal when their
  `obj` and `map` fields agree.  The `map` field's type depends on
  `obj`, so the natural statement uses `HEq` on the maps.

  comp-cat-theory does not (yet) ship a `Functor.ext` lemma; this
  module fills the gap locally and uses it to close the Phase 1a
  group-action laws in `Bridge.ArrowImpossibility`.

  Could plausibly upstream to comp-cat-theory; kept here for now.
-/

import CompCatTheory.Foundation.Category

set_option autoImplicit false

universe u₁ v₁ u₂ v₂

namespace UnifiedAggregation

open CompCatTheory

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

end UnifiedAggregation
