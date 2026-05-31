/-
  UnifiedAggregation.Aggregation

  Aggregation as a left Kan extension along the orbit projection
  p : C ⥤ C // G into the action groupoid.

  The action groupoid `C // G` is structurally wrapped (rather than a
  bare `def := Obj`) to keep the Category instance from colliding with
  C's own Category instance via recursive typeclass lookup.  Morphisms
  are pairs `(g, f : X.val → act(g)(Y.val))`; identity uses `act_one`
  to cast `𝟙 X.val` into the orbit-typed form; composition uses
  `act_mul` to bundle the group element with the transported C-morphism.

  The three Category laws (`comp_id`, `id_comp`, `assoc`) on the orbit
  groupoid plus the two Functor laws on `orbitProjection` (`map_id`,
  `map_comp`) are sorried in this commit and tracked as Phase 1a
  follow-up — each is a multi-step rewrite through the cast machinery.
-/

import UnifiedAggregation.ChoiceRule
import UnifiedAggregation.HeqTransport
import CompCatTheory.Primitive.KanExtension

set_option autoImplicit false

universe u v w

namespace UnifiedAggregation

open CompCatTheory Category Functor

/-- The carrier type for the *orbit groupoid* `C // G`.  Wrapped in a
structure (rather than a `def := Obj`) so the Category instance below
doesn't collide with `C`'s own Category instance through recursive
typeclass lookup. -/
structure OrbitGroupoid {Obj : Type u} [Category.{u, u} Obj]
    {G : SymmetryGroup.{w}} (_act : GAction G Obj) : Type u where
  val : Obj

/-- A *morphism in the orbit groupoid* from `X` to `Y`: a pair `(g, f)`
where `g : G.carrier` and `f : Hom X.val (act(g)(Y.val))`.  Intuitively
this is a C-morphism from the underlying value of `X` to a chosen
representative of `Y`'s orbit, with `g` recording the choice. -/
structure OrbitHom {Obj : Type u} [Category.{u, u} Obj]
    {G : SymmetryGroup.{w}} (act : GAction G Obj)
    (X Y : OrbitGroupoid act) : Type (max u w) where
  g : G.carrier
  f : Hom X.val ((act.act g).obj Y.val)

/-- Extensionality for `OrbitHom`: two orbit morphisms are equal iff
their `g` and `f` fields agree.  The `f` field's type depends on `g`,
so the `f`-equality is stated using `HEq`.  After destructuring and
the `rfl + HEq.refl` patterns align everything, `rfl` closes. -/
theorem OrbitHom.ext {Obj : Type u} [Category.{u, u} Obj]
    {G : SymmetryGroup.{w}} {act : GAction G Obj}
    {X Y : OrbitGroupoid act} : ∀ {p q : OrbitHom act X Y},
    p.g = q.g → HEq p.f q.f → p = q
  | ⟨_, _⟩, ⟨_, _⟩, rfl, HEq.refl _ => rfl

/-- The orbit groupoid carries a category structure.  `Hom`, `id`, and
`comp` are wired to the `OrbitHom` machinery; the three associativity-
and-unit laws are sorried (each is a multi-step rewrite through the
cast machinery and is tracked as Phase 1a follow-up). -/
instance orbitGroupoidCategory {Obj : Type u} [Category.{u, u} Obj]
    {G : SymmetryGroup.{w}} {act : GAction G Obj} :
    Category.{u, max u w} (OrbitGroupoid act) where
  Hom X Y := OrbitHom act X Y
  id X := { g := G.one, f := act.act_one.symm ▸ (𝟙 X.val) }
  comp p q :=
    { g := G.mul p.g q.g
      f := (act.act_mul p.g q.g).symm ▸ (p.f ≫ (act.act p.g).map q.f) }
  -- The g-field of each law closes by direct application of the
  -- corresponding SymmetryGroup law (mul_one, one_mul, mul_assoc).
  -- The HEq on the f-field follows the same template as the
  -- `orbitProjection.map_comp` closure below (heq_strip + heq_comp
  -- + idFunctor collapse) but with additional `Functor.map_id` /
  -- `Category.comp_id` / `Category.id_comp` reductions inside the
  -- composition.  Sorried pending the next round.
  comp_id := fun p => by
    apply OrbitHom.ext
    · exact G.mul_one p.g
    · sorry
  id_comp := fun p => by
    apply OrbitHom.ext
    · exact G.one_mul p.g
    · sorry
  assoc := fun p q r => by
    apply OrbitHom.ext
    · exact G.mul_assoc p.g q.g r.g
    · sorry

/-- The orbit projection `p : C ⥤ C // G`.  Sends each C-object to its
wrapped form in `OrbitGroupoid` and each C-morphism `f : X → Y` to the
orbit morphism `(G.one, f)` with the `act_one` cast.  Functoriality
laws (`map_id`, `map_comp`) are sorried; both follow from the orbit
groupoid laws plus the cast machinery. -/
def orbitProjection {Obj : Type u} [Category.{u, u} Obj]
    {G : SymmetryGroup.{w}} (act : GAction G Obj) :
    Obj ⥤ OrbitGroupoid act where
  obj X := { val := X }
  map {_ _} f := { g := G.one, f := act.act_one.symm ▸ f }
  map_id _ := rfl
  map_comp {X Y Z} f g := by
    apply OrbitHom.ext
    · exact (G.one_mul G.one).symm
    · -- `heq_strip` peels the outer `act.act_one` / `act.act_mul`
      -- casts on each side.  The interleaved `dsimp only []`
      -- reduces structure-literal projections exposed by the
      -- composition unfold after the first pass.
      dsimp only []
      heq_strip
      dsimp only []
      heq_strip
      -- Residual: `HEq (f ≫ g) (cast_f ≫ (act.act G.one).map cast_g)`.
      -- Close via HEq congruence for `≫` plus the `idFunctor`
      -- collapse of `act.act G.one`.  Motive made explicit
      -- (Lean's higher-order inference for `▸` with
      -- `fun F => Hom X (F.obj Y)`-shaped motives is ambiguous).
      refine heq_comp ?_ ?_ ?_ ?_
      · exact (idFunctor_obj_eq act.act_one _).symm
      · exact (idFunctor_obj_eq_twice act.act_one _).symm
      · exact (eqRec_heq_dep (motive := fun F _ => Hom X (F.obj Y))
          act.act_one.symm f).symm
      · exact HEq.trans (eqRec_heq_dep
          (motive := fun F _ => Hom Y (F.obj Z))
          act.act_one.symm g).symm
          (idFunctor_map_heq act.act_one _).symm

/-- **Aggregation** is the *left Kan extension* of a choice rule
`F : C ⥤ D` along the orbit projection `p : C ⥤ C // G`.

This is the central object of the unified theory.  Each of the three
regimes (Arrow-Debreu, Arrow-Impossibility, Schelling-Ising) is a
property of when and how this Kan extension is realized:

- Arrow-Debreu: realized uniquely (convex case)
- Arrow-Impossibility: no realization satisfies the equivariance,
  unanimity, and IIA-as-naturality constraints
- Schelling-Ising: multiple non-isomorphic realizations bifurcate with
  the β parameter -/
def Aggregation
    {Obj : Type u} [Category.{u, u} Obj]
    {G : SymmetryGroup.{w}} (act : GAction G Obj)
    {D : Type v} [Category.{v, v} D]
    (F : ChoiceRule Obj D) :=
  LeftKanExtension (orbitProjection act) F

end UnifiedAggregation
