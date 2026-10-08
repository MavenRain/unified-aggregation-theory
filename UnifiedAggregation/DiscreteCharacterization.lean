/-
  UnifiedAggregation.DiscreteCharacterization

  The full characterization of aggregation into a *discrete* outcome
  category.  `Characterization.lan_implies_orbit_constant` gives one
  direction: an aggregation forces the choice rule to be constant on
  orbits.  This module supplies the converse and the uniqueness facts:

  1. `orbitConstantAggregation`: an orbit-constant discrete choice rule
     has an aggregation.  The Kan extension is built by hand: the
     extended functor sends an orbit-groupoid object `⟨x⟩` to `F.obj x`,
     and an orbit morphism `(g, f : x ⟶ act g y)` to the discrete
     morphism forced by `F.map f` and orbit constancy at `(g, y)`.

  2. `aggregation_nonempty_iff_orbitConstant`: an aggregation exists
     exactly when the choice rule is constant on orbits.

  3. `aggregation_obj_unique` / `aggregation_obj_eq_rule`: any two
     aggregations of one rule agree on *every* object of the orbit
     groupoid (not only on the image of the orbit projection, which is
     all of it: `orbitProjection_obj_surjective`), and every aggregation
     sends `⟨x⟩` to `F.obj x`.

  Every hom-set of a discrete category is a subsingleton
  (`discreteHom_subsingleton`), so all naturality, factorization and
  uniqueness obligations close by that one lemma.

  All proofs are term-mode;  no tactic blocks.
-/

import UnifiedAggregation.Characterization

set_option autoImplicit false

universe u v w

namespace UnifiedAggregation

open CompCatTheory Category Functor

/-- A choice rule is *constant on orbits* when it takes the same value on
`x` and on `act g x` for every group element `g`.  This is the
conclusion of `lan_implies_orbit_constant`, packaged as a predicate. -/
def OrbitConstant
    {Obj : Type u} [Category.{u, u} Obj]
    {G : SymmetryGroup.{w}} (act : GAction G Obj)
    {D : Type v} [Category.{v, v} D]
    (F : ChoiceRule Obj D) : Prop :=
  ∀ (g : G.carrier) (x : Obj), F.obj ((act.act g).obj x) = F.obj x

/-- Any two morphisms with the same endpoints in a discrete category are
equal:  `DiscreteHom`'s only constructor is the identity. -/
theorem discreteHom_subsingleton {α : Type v} {X Y : Discrete α}
    (h₁ h₂ : DiscreteHom X Y) : h₁ = h₂ :=
  match h₁, h₂ with
  | .id .., .id .. => rfl

/-- The discrete morphism carried by an object equality. -/
def discreteHomOfEq {α : Type v} {X Y : Discrete α}
    (h : X = Y) : DiscreteHom X Y :=
  cast (congrArg (DiscreteHom X) h) (DiscreteHom.id X)

/-- Every object of the orbit groupoid is the orbit projection of its
underlying value:  the orbit projection is surjective on objects. -/
theorem orbitProjection_obj_surjective
    {Obj : Type u} [Category.{u, u} Obj]
    {G : SymmetryGroup.{w}} (act : GAction G Obj)
    (Y : OrbitGroupoid act) :
    (orbitProjection act).obj Y.val = Y :=
  rfl

/-- The extended functor of an orbit-constant discrete choice rule.  An
orbit morphism `(g, f : x ⟶ act g y)` maps to the discrete morphism
forced by `F.map f : F x ⟶ F (act g y)` and orbit constancy
`F (act g y) = F y`. -/
def orbitConstantLift
    {Obj : Type u} [Category.{u, u} Obj]
    {G : SymmetryGroup.{w}} {act : GAction G Obj} {α : Type v}
    (F : ChoiceRule Obj (Discrete α)) (hF : OrbitConstant act F) :
    OrbitGroupoid act ⥤ Discrete α where
  obj X := F.obj X.val
  map {_X Y} p :=
    discreteHomOfEq
      ((discreteHom_eq (F.map (OrbitHom.f p))).trans (hF (OrbitHom.g p) Y.val))
  map_id _X := discreteHom_subsingleton _ _
  map_comp _f _g := discreteHom_subsingleton _ _

/-- **Converse of `lan_implies_orbit_constant`.**  An orbit-constant
choice rule into a discrete category has an aggregation:  the left Kan
extension along the orbit projection is `orbitConstantLift`, with the
identity unit.  The mediating transformation out of it into any cocone
`β : F ⟹ p ⋙ M` has component `β.app x` at `⟨x⟩`;  naturality,
factorization and uniqueness hold because discrete hom-sets are
subsingletons. -/
def orbitConstantAggregation
    {Obj : Type u} [Category.{u, u} Obj]
    {G : SymmetryGroup.{w}} {act : GAction G Obj} {α : Type v}
    (F : ChoiceRule Obj (Discrete α)) (hF : OrbitConstant act F) :
    Aggregation act F where
  functor := orbitConstantLift F hF
  unit :=
    { app := fun x => DiscreteHom.id (F.obj x)
      naturality := fun (_f) => discreteHom_subsingleton _ _ }
  desc := fun β =>
    { app := fun X => β.app X.val
      naturality := fun (_f) => discreteHom_subsingleton _ _ }
  fac := fun (_β) (_x) => discreteHom_subsingleton _ _
  uniq := fun (_α) (_β) (_h) (_Y) => discreteHom_subsingleton _ _

/-- **Aggregation into a discrete category exists exactly for the
orbit-constant choice rules.**  Forward:  `lan_implies_orbit_constant`.
Backward:  `orbitConstantAggregation`.

Universes match `lan_implies_orbit_constant` (the group, the
configuration category and the outcome type share `u`);  the backward
construction `orbitConstantAggregation` is universe-polymorphic. -/
theorem aggregation_nonempty_iff_orbitConstant
    {Obj : Type u} [Category.{u, u} Obj]
    {G : SymmetryGroup.{u}} {act : GAction G Obj} {α : Type u}
    (F : ChoiceRule Obj (Discrete α)) :
    Nonempty (Aggregation act F) ↔ OrbitConstant act F :=
  ⟨fun ⟨L⟩ => lan_implies_orbit_constant F L,
   fun hF => ⟨orbitConstantAggregation F hF⟩⟩

/-- **Every aggregation into a discrete category is pinned to the
choice rule on objects:**  it sends `⟨x⟩` to `F.obj x`.  The unit
component at `x` is a discrete morphism, hence an equality. -/
theorem aggregation_obj_eq_rule
    {Obj : Type u} [Category.{u, u} Obj]
    {G : SymmetryGroup.{w}} {act : GAction G Obj} {α : Type v}
    (F : ChoiceRule Obj (Discrete α))
    (L : Aggregation act F) (Y : OrbitGroupoid act) :
    L.functor.obj Y = F.obj Y.val :=
  (discreteHom_eq (L.unit.app Y.val)).symm

/-- **Object-uniqueness of aggregations into a discrete category.**  Any
two aggregations of one choice rule have equal object maps at every
object of the orbit groupoid.  This is `lan_obj_unique_discrete` at the
orbit projection;  it holds on all objects, not only on the image of
`orbitProjection` (which is everything, by
`orbitProjection_obj_surjective`). -/
theorem aggregation_obj_unique
    {Obj : Type u} [Category.{u, u} Obj]
    {G : SymmetryGroup.{w}} {act : GAction G Obj} {α : Type v}
    {F : ChoiceRule Obj (Discrete α)}
    (L₁ L₂ : Aggregation act F) (Y : OrbitGroupoid act) :
    L₁.functor.obj Y = L₂.functor.obj Y :=
  lan_obj_unique_discrete L₁ L₂ Y

end UnifiedAggregation
