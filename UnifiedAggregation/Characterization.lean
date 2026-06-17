/-
  UnifiedAggregation.Characterization

  The two structural facts that turn the trichotomy from a vacuous
  taxonomy into a content-bearing classification:

  1. `lan_obj_unique_discrete` / `not_schelling_ising_discrete`:
     into a *discrete* target, any two left Kan extensions agree on
     objects, so `IsSchellingIsingRegime` is uninhabitable.  This is the
     precise reason the original discrete encoding could never realize a
     symmetry-broken phase, and it is why the genuine Schelling-Ising
     witness must use a non-rigid (indiscrete / phase) target.

  2. `lan_implies_orbit_constant`: into a discrete target, the existence
     of a left Kan extension along the orbit projection forces the
     choice rule to be constant on orbits (the anonymity / equivariance
     condition).  Contrapositive: a non-anonymous choice rule has *no*
     Kan extension, i.e. it sits in the Arrow-Impossibility regime.
     This is the bridge that makes Arrow's theorem a genuine regime
     witness (a Pareto+IIA social welfare function is forced
     non-anonymous, hence has no aggregation).

  All proofs are term-mode; no tactic blocks.
-/

import UnifiedAggregation.Regimes
import UnifiedAggregation.Discrete

set_option autoImplicit false

universe u v u₁ v₁ u₂ v₂ u₃

namespace UnifiedAggregation

open CompCatTheory Category Functor

/-- A morphism in a discrete category forces its endpoints to be equal:
`DiscreteHom`'s only constructor is the identity. -/
theorem discreteHom_eq {α : Type u} {X Y : Discrete α}
    (h : DiscreteHom X Y) : X = Y :=
  match h with
  | .id _ => rfl

/-- **Object-uniqueness of left Kan extensions into a discrete target.**
Any two left Kan extensions of `F` along `K` agree on objects.

Proof: `L₁.desc L₂.unit : L₁.functor ⟹ L₂.functor` is a natural
transformation; its component at `Y` is a morphism in the discrete
target, which forces `L₁.functor.obj Y = L₂.functor.obj Y`.  (Only one
mediating natural transformation is needed -- not the full isomorphism
-- because a single discrete morphism already pins the objects.) -/
theorem lan_obj_unique_discrete
    {J : Type u₁} {C : Type u₂} {α : Type u₃}
    [Category.{u₁, v₁} J] [Category.{u₂, v₂} C]
    {K : J ⥤ C} {F : J ⥤ Discrete α}
    (L₁ L₂ : LeftKanExtension K F) (Y : C) :
    L₁.functor.obj Y = L₂.functor.obj Y :=
  discreteHom_eq ((L₁.desc L₂.unit).app Y)

/-- **The Schelling-Ising regime is empty over a discrete target.**
This is the counterexample that motivated the phase-groupoid target:
object-level non-uniqueness of an aggregation cannot occur when the
outcome category is discrete (isomorphic objects are equal there). -/
theorem not_schelling_ising_discrete
    {Obj : Type u} [Category.{u, u} Obj]
    {G : SymmetryGroup.{u}} {act : GAction G Obj} {α : Type u}
    (F : ChoiceRule Obj (Discrete α)) :
    ¬ IsSchellingIsingRegime act F :=
  fun ⟨L₁, L₂, Y, hne⟩ => hne (lan_obj_unique_discrete L₁ L₂ Y)

/-- **Existence of an aggregation forces constancy on orbits.**
If a left Kan extension of `F` along the orbit projection exists and the
target is discrete, then `F` takes equal values on `x` and `act g x` for
every group element `g`: the choice rule is anonymous / equivariant.

Proof: the unit gives `F.obj y = L.functor.obj ⟨y⟩` for every `y` (a
discrete morphism, hence object equality).  The orbit groupoid carries a
morphism `⟨act g x⟩ ⟶ ⟨x⟩` (namely `(g, 𝟙)`), and `L.functor` sends it
to a discrete morphism, forcing `L.functor.obj ⟨act g x⟩ =
L.functor.obj ⟨x⟩`.  Chaining the three equalities gives the claim. -/
theorem lan_implies_orbit_constant
    {Obj : Type u} [Category.{u, u} Obj]
    {G : SymmetryGroup.{u}} {act : GAction G Obj} {α : Type u}
    (F : ChoiceRule Obj (Discrete α))
    (L : Aggregation act F) (g : G.carrier) (x : Obj) :
    F.obj ((act.act g).obj x) = F.obj x :=
  let e : ∀ y, F.obj y = L.functor.obj ((orbitProjection act).obj y) :=
    fun y => discreteHom_eq (L.unit.app y)
  let φ : Hom ((orbitProjection act).obj ((act.act g).obj x))
              ((orbitProjection act).obj x) :=
    { g := g, f := 𝟙 ((act.act g).obj x) }
  let mid : L.functor.obj ((orbitProjection act).obj ((act.act g).obj x))
          = L.functor.obj ((orbitProjection act).obj x) :=
    discreteHom_eq (L.functor.map φ)
  (e ((act.act g).obj x)).trans (mid.trans (e x).symm)

end UnifiedAggregation
