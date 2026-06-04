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

import KanTactics
import CompCatTheory.Foundation.Category

set_option autoImplicit false

universe u₁ v₁ u₂ v₂

namespace UnifiedAggregation

open CompCatTheory Category

/-- The map-level `HEq` that the pointwise functor extensionality needs:
given object maps `Fo`, `Go` that are equal *as functions* and morphism
maps that agree pointwise (as `HEq`), the bundled morphism maps are `HEq`.

Stating `Fo`/`Go` as plain function variables (rather than the `obj`
*field projection* of a functor) is what lets `kan_subst` fire: the
equation `ho : Fo = Go` has a free variable on each side, so the
substitution Kan extension aligns the two map types definitionally,
after which the pointwise `HEq`s collapse to a function `Eq` lifted back
to `HEq`. -/
private theorem functorMapHEq {C : Type u₁} {D : Type u₂}
    [Category.{u₁, v₁} C] [Category.{u₂, v₂} D] {Fo Go : C → D}
    {Fm : {X Y : C} → Hom X Y → Hom (Fo X) (Fo Y)}
    {Gm : {X Y : C} → Hom X Y → Hom (Go X) (Go Y)}
    (ho : Fo = Go)
    (hm : ∀ {X Y : C} (f : Hom X Y), HEq (Fm f) (Gm f)) :
    HEq @Fm @Gm := by
  kan_subst ho
  kan_exact heq_of_eq
    (funext (fun (X : C) => funext (fun (Y : C) => funext (fun (f : Hom X Y) =>
      eq_of_heq (hm f)))))

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
recipe.

Proof: term mode, reducing to `Functor.ext` by supplying the bundled
object equality `funext h_obj` and the bundled map `HEq` produced by
`functorMapHEq` (whose `kan_subst` aligns the two map types). -/
theorem Functor.ext_pointwise {C : Type u₁} {D : Type u₂}
    [Category.{u₁, v₁} C] [Category.{u₂, v₂} D]
    (F G : C ⥤ D)
    (h_obj : ∀ X : C, F.obj X = G.obj X)
    (h_map : ∀ {X Y : C} (f : Hom X Y), HEq (F.map f) (G.map f)) :
    F = G :=
  Functor.ext (funext h_obj) (functorMapHEq (funext h_obj) h_map)

end UnifiedAggregation
