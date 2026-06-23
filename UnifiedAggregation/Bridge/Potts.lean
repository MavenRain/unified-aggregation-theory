/-
  UnifiedAggregation.Bridge.Potts

  The q-state Potts instantiation of the trichotomy: the same single
  `Aggregation` construction (left Kan extension along the orbit
  projection), now driven by the symmetric group `S_q` acting on
  n-ary spins, realizes all three regimes.

  This generalizes `Bridge.SchellingIsing` from the binary `Z_2` spin
  (`q = 2`, the Ising case) to a `q`-ary Potts spin with the full
  permutation symmetry `S_q` on the colours.  Crucially, NOTHING in the
  categorical core changes: `Aggregation`, `orbitProjection`, the three
  `Regime` predicates, the discrete-target obstruction, the indiscrete
  phase target, and `Trichotomy.trichotomy` are all polymorphic in the
  symmetry group, so swapping `Z2Group` for `SymmetricGroup q` is a
  drop-in.  What this module adds is the q-state WITNESS data:

  Categorical embedding:
  - `PottsConfig n q` = `Fin n -> Fin q` with the `S_q` colour action
  - `pottsConfigAction : GAction (SymmetricGroup q) (PottsConfigCat n q)`

  Order parameter and mean-field fixed points:
  - `PottsFixedPoint q beta x`: a per-colour mean-field self-consistency,
    the vector analogue of `SchellingIsing.IsMeanFieldFixedPoint` (each
    colour coordinate independently satisfies the rational sigmoid
    fixed-point equation).  This is a faithful but schematic rational
    surrogate, in the same spirit as the `Z_2` file's `tanh -> x/(1+|x|)`
    substitution: it captures the q-fold `S_q`-orbit of symmetry-broken
    phases, which is what the regime classification sees.  It does NOT
    model the genuinely first-order Curie-Weiss-Potts transition (the
    saddle-node birth, the `(q-2)/(q-1)` discontinuous jump); that is a
    separate analytic refinement and is not needed to INHABIT the regimes.

  The three regime witnesses (all on the one `pottsConfigAction`):
  - `potts_arrow_impossibility_regime`: a non-orbit-constant discrete
    choice rule has no aggregation (via `lan_implies_orbit_constant`).
  - `potts_disordered_arrow_debreu_regime` (`beta <= 1`): the uniform
    phase is the unique fixed point, so the aggregation is object-unique.
  - `potts_ordered_schelling_ising_regime` (`beta > 1`): two ordered
    phases from the `S_q`-orbit are distinct fixed points, so the
    aggregation is object-non-unique.

  Capstone:
  - `potts_trichotomy_holds`: the generic `trichotomy`, instantiated at
    the Potts action, for ANY choice rule (the "stays intact" statement).
  - `potts_trichotomy_regimes_realized`: all three regimes are genuinely
    inhabited by the single Potts `Aggregation` construction.

  kan-tactics only in tactic blocks; arithmetic and case analysis with no
  Kan surface are term mode (which the convention permits).  No Mathlib.
-/

import KanTactics
import UnifiedAggregation.Discrete
import UnifiedAggregation.SymmetricGroup
import UnifiedAggregation.FunctorExt
import UnifiedAggregation.Aggregation
import UnifiedAggregation.Regimes
import UnifiedAggregation.Indiscrete
import UnifiedAggregation.Characterization
import UnifiedAggregation.Trichotomy
import UnifiedAggregation.Bridge.SchellingIsing

set_option autoImplicit false

namespace UnifiedAggregation.Bridge

open CompCatTheory

universe v

/-! ## n-ary spins and the `S_q` colour action

A Potts configuration assigns one of `q` colours to each of `n` sites.
The symmetry group is `S_q`, acting by permuting the colour labels (the
`q = 2` Ising case recovers the single `Z_2` flip).  The action on a
configuration is post-composition of the colour permutation with the
configuration; we use `invFun` so the homomorphism law matches the
framework's `act (g * h) = act h ⋙ act g` convention (a left action). -/

/-- A configuration of `n` Potts spins, each taking one of `q` colours. -/
def PottsConfig (n q : Nat) : Type := Fin n → Fin q

/-- `S_q` acts on a Potts configuration by relabelling colours.  Using
`σ.invFun` (rather than `σ.toFun`) makes this a left action compatible
with the `act (g * h) = act h ⋙ act g` convention, since
`(σ.comp τ).invFun = σ.invFun ∘ τ.invFun`. -/
def Potts.actOnConfig {n q : Nat} (σ : Perm q) (c : PottsConfig n q) :
    PottsConfig n q :=
  fun i => σ.invFun (c i)

/-- The identity permutation acts as identity (definitional: `Perm.id`'s
`invFun` is `id`, and function eta closes the rest). -/
theorem Potts.actOnConfig_one {n q : Nat} (c : PottsConfig n q) :
    Potts.actOnConfig (Perm.id q) c = c := rfl

/-- The action respects composition (definitional: `(σ.comp τ).invFun x`
unfolds to `σ.invFun (τ.invFun x)`, matching the right-hand side). -/
theorem Potts.actOnConfig_mul {n q : Nat} (σ τ : Perm q) (c : PottsConfig n q) :
    Potts.actOnConfig (Perm.comp σ τ) c
      = Potts.actOnConfig σ (Potts.actOnConfig τ c) := rfl

/-- The configuration category for Potts: discrete category on
configurations. -/
abbrev PottsConfigCat (n q : Nat) : Type := Discrete (PottsConfig n q)

/-- The endofunctor on `PottsConfigCat n q` induced by an `S_q` element,
acting pointwise by colour relabelling. -/
def Potts.configActBy {n q : Nat} (σ : Perm q) :
    PottsConfigCat n q ⥤ PottsConfigCat n q :=
  discreteFunctor (Potts.actOnConfig σ)

/-- The `S_q` action on `PottsConfig n q` lifted to a `GAction` on the
discrete configuration category.

Both `act_one` and `act_mul` close through the standard `Functor.ext`
recipe (object equality by `rfl`, the single discrete `.id` morphism's
`HEq` by a match).  Unlike the `Z_2` `spinConfigAction`, no pointwise
`flip_flip` detour is needed: the object fields agree DEFINITIONALLY
because `Perm.comp`'s `invFun` is by construction the composed inverse,
so `actOnConfig (σ.comp τ) = actOnConfig σ ∘ actOnConfig τ` holds by
`rfl`. -/
def pottsConfigAction (n q : Nat) :
    GAction (SymmetricGroup q) (PottsConfigCat n q) where
  act := Potts.configActBy
  act_one :=
    UnifiedAggregation.Functor.ext
      (funext (fun _ => rfl))
      (heq_of_eq (funext (fun _ => funext (fun _ => funext (fun h =>
        match h with
        | DiscreteHom.id _ => rfl)))))
  act_mul _ _ :=
    UnifiedAggregation.Functor.ext
      (funext (fun _ => rfl))
      (heq_of_eq (funext (fun _ => funext (fun _ => funext (fun h =>
        match h with
        | DiscreteHom.id _ => rfl)))))

/-! ## Mean-field order parameter and fixed points

The Potts order parameter is a vector `x : Fin q -> Rat` of per-colour
fields, generalizing the scalar Ising magnetization.  A configuration of
fields is a mean-field fixed point when each colour coordinate satisfies
the same rational sigmoid self-consistency used in `SchellingIsing`.
This per-colour predicate is symmetric under colour permutations, so its
fixed-point set is closed under the `S_q` action (`pottsFixedPoint_perm`):
the symmetry-broken phases come in `S_q`-orbits of size `q` (one dominant
colour each), the q-state generalization of the `Z_2` pair `±m_*`. -/

/-- A vector of per-colour fields is a Potts mean-field fixed point when
every colour coordinate independently solves the scalar self-consistency
`IsMeanFieldFixedPoint` from `SchellingIsing`. -/
def PottsFixedPoint (q : Nat) (β : Rat) (x : Fin q → Rat) : Prop :=
  ∀ a : Fin q, IsMeanFieldFixedPoint β (x a)

/-- The fixed-point set is closed under the `S_q` colour action: if `x`
is a fixed point then so is its coordinate permutation.  This is the
`S_q`-equivariance that replaces the `Z_2` oddness `m ↦ -m`
(`Magnetization_flip`): the symmetry-broken phases form a genuine
`S_q`-orbit. -/
theorem pottsFixedPoint_perm {q : Nat} {β : Rat} (σ : Perm q)
    {x : Fin q → Rat} (hx : PottsFixedPoint q β x) :
    PottsFixedPoint q β (fun a => x (σ.toFun a)) :=
  fun a => hx (σ.toFun a)

/-- The symmetric (disordered) order parameter: all colour fields zero. -/
def pottsUniform (q : Nat) : Fin q → Rat := fun _ => 0

/-- The disordered order parameter is a fixed point at every `β`. -/
theorem pottsUniform_fixed (q : Nat) (β : Rat) :
    PottsFixedPoint q β (pottsUniform q) :=
  fun _ => zero_is_fixed_point β

/-- The **phase category** at inverse temperature `β`: the indiscrete
groupoid on the set of Potts mean-field fixed points.  Objects are the
order-parameter vectors the system can settle into; the unique morphism
between any two encodes their physical equivalence under the colour
symmetry. -/
abbrev PottsPhase (q : Nat) (β : Rat) : Type :=
  Indiscrete {x : Fin q → Rat // PottsFixedPoint q β x}

/-- The disordered reference phase. -/
def pottsUniformPhase (q : Nat) (β : Rat) : PottsPhase q β :=
  Indiscrete.mk ⟨pottsUniform q, pottsUniform_fixed q β⟩

/-- The `S_q`-symmetric choice rule sending every configuration to the
disordered reference phase.  Spontaneous symmetry breaking is the
statement that, even though this rule is symmetric, its aggregation need
not be object-unique above the critical temperature. -/
def pottsChoiceRule (n q : Nat) (β : Rat) : PottsConfigCat n q ⥤ PottsPhase q β :=
  constIndiscrete (pottsUniformPhase q β)

/-! ## Arrow-Debreu regime (disordered phase, `β ≤ 1`) -/

/-- Below the critical temperature the only fixed point is the uniform
vector: each coordinate is forced to `0` by `unique_fixed_point_paramagnetic`. -/
theorem pottsFixedPoint_below {q : Nat} {β : Rat} (hβ : β ≤ 1)
    {x : Fin q → Rat} (hx : PottsFixedPoint q β x) : x = pottsUniform q :=
  funext (fun a => unique_fixed_point_paramagnetic β hβ (x a) (hx a))

/-- For `β ≤ 1` the phase category is a subsingleton: every fixed point
is the uniform vector, so all objects of `PottsPhase β` are equal. -/
theorem pottsPhase_subsingleton {q : Nat} {β : Rat} (hβ : β ≤ 1) :
    ∀ a b : PottsPhase q β, a = b :=
  fun a b =>
    congrArg Indiscrete.mk
      (Subtype.ext
        ((pottsFixedPoint_below hβ a.val.property).trans
          (pottsFixedPoint_below hβ b.val.property).symm))

/-- **Arrow-Debreu regime witness (disordered phase, `β ≤ 1`).**  The
aggregation of the symmetric choice rule exists and is object-unique,
because the only fixed point is the uniform vector: the equilibrium
order parameter is uniquely determined.  Same `Aggregation` construction
as every other regime; the regime is forced by `pottsPhase_subsingleton`. -/
theorem potts_disordered_arrow_debreu_regime (n q : Nat) {β : Rat} (hβ : β ≤ 1) :
    IsArrowDebreuRegime (pottsConfigAction n q) (pottsChoiceRule n q β) :=
  ⟨indiscreteLan (orbitProjection (pottsConfigAction n q)) (pottsChoiceRule n q β)
      (pottsUniformPhase q β),
   fun _ _ => pottsPhase_subsingleton hβ _ _⟩

/-! ## Schelling-Ising regime (ordered phase, `β > 1`)

The symmetry-broken phases are the `S_q`-orbit of "condense on one
colour" states.  We build the explicit ordered order parameter that puts
a nonzero field `m` on colour `a` and zero elsewhere, and exhibit two of
them (different dominant colours) as distinct fixed points.  Distinctness
is exactly `m ≠ 0`, supplied by `bifurcation_ferromagnetic`. -/

/-- The ordered order parameter condensing on colour `a` with field `m`:
colour `a` carries `m`, every other colour carries `0`. -/
def pottsOrdered (q : Nat) (a : Fin q) (m : Rat) : Fin q → Rat :=
  fun b => if b = a then m else 0

/-- Value of the ordered parameter on its dominant colour. -/
theorem pottsOrdered_apply_self {q : Nat} (a : Fin q) (m : Rat) :
    pottsOrdered q a m a = m := if_pos rfl

/-- Value of the ordered parameter on its dominant colour, witnessed by a
proof `b = a`. -/
theorem pottsOrdered_apply_eq {q : Nat} {a b : Fin q} (hb : b = a) (m : Rat) :
    pottsOrdered q a m b = m := if_pos hb

/-- Value of the ordered parameter on a non-dominant colour. -/
theorem pottsOrdered_apply_other {q : Nat} {a b : Fin q} (hab : b ≠ a) (m : Rat) :
    pottsOrdered q a m b = 0 := if_neg hab

/-- The ordered parameter is a fixed point whenever its field value is:
each coordinate is either `m` (a fixed point by hypothesis) or `0` (a
fixed point by `zero_is_fixed_point`).  The `Eq.mpr (congrArg …)` casts
transport the scalar fixed-point facts along the per-colour value
equalities (the `pottsOrdered q a m b` subterm appears verbatim, so the
predicate-level rewrite is unambiguous). -/
theorem pottsOrdered_fixed {q : Nat} {β : Rat} (a : Fin q) {m : Rat}
    (hm : IsMeanFieldFixedPoint β m) : PottsFixedPoint q β (pottsOrdered q a m) :=
  fun b =>
    if hb : b = a then
      Eq.mpr (congrArg (IsMeanFieldFixedPoint β) (pottsOrdered_apply_eq hb m)) hm
    else
      Eq.mpr (congrArg (IsMeanFieldFixedPoint β) (pottsOrdered_apply_other hb m))
        (zero_is_fixed_point β)

/-- `(0 : Fin q) ≠ (1 : Fin q)` for `q ≥ 2`, packaged for the colour
indices used below. -/
theorem fin_zero_ne_one {q : Nat} (h0 : 0 < q) (h1 : 1 < q) :
    (⟨0, h0⟩ : Fin q) ≠ ⟨1, h1⟩ :=
  fun h => Nat.noConfusion (congrArg Fin.val h)

/-- **Schelling-Ising regime witness (ordered phase, `β > 1`).**  The
aggregation of the *same* symmetric choice rule exists but is *not*
object-unique: two ordered phases from the `S_q`-orbit (condensing on
colour `0` versus colour `1`) are distinct fixed points, hence two left
Kan extensions whose object-assignments differ.  Spontaneous symmetry
breaking realized as genuine non-uniqueness of the universal aggregate,
impossible over a discrete target (`not_schelling_ising_discrete`), which
is why the phase groupoid is needed. -/
theorem potts_ordered_schelling_ising_regime (n q : Nat) (hq : 1 < q)
    {β : Rat} (hβ : 1 < β) :
    IsSchellingIsingRegime (pottsConfigAction n q) (pottsChoiceRule n q β) :=
  match bifurcation_ferromagnetic β hβ with
  | ⟨m₁, _m₂, _hne, hm₁0, _hm₂0, h₁, _h₂⟩ =>
    let h0 : 0 < q := Nat.lt_of_le_of_lt (Nat.zero_le 1) hq
    let c0 : Fin q := ⟨0, h0⟩
    let c1 : Fin q := ⟨1, hq⟩
    let A : {x : Fin q → Rat // PottsFixedPoint q β x} :=
      ⟨pottsOrdered q c0 m₁, pottsOrdered_fixed c0 h₁⟩
    let B : {x : Fin q → Rat // PottsFixedPoint q β x} :=
      ⟨pottsOrdered q c1 m₁, pottsOrdered_fixed c1 h₁⟩
    ⟨indiscreteLan (orbitProjection (pottsConfigAction n q)) (pottsChoiceRule n q β)
        (Indiscrete.mk A),
     indiscreteLan (orbitProjection (pottsConfigAction n q)) (pottsChoiceRule n q β)
        (Indiscrete.mk B),
     ⟨⟨fun _ => c0⟩⟩,
     Indiscrete.mk_ne
       (fun hAB =>
         hm₁0
           (let hval : pottsOrdered q c0 m₁ = pottsOrdered q c1 m₁ :=
              congrArg Subtype.val hAB
            let hc0 : pottsOrdered q c0 m₁ c0 = pottsOrdered q c1 m₁ c0 :=
              congrFun hval c0
            ((pottsOrdered_apply_self c0 m₁).symm.trans hc0).trans
              (pottsOrdered_apply_other (fin_zero_ne_one h0 hq) m₁)))⟩

/-! ## Arrow-Impossibility regime (non-anonymous rule on the Potts action)

A discrete-target choice rule that is not constant on `S_q`-orbits has no
aggregation, by the contrapositive of `lan_implies_orbit_constant`.  We
witness non-orbit-constancy with the identity discrete rule and a colour
transposition that genuinely moves a configuration. -/

/-- The colour-swap function exchanging colours `0` and `1`, fixing the
rest.  An involution, used to build the transposition permutation. -/
def Potts.swapFn (q : Nat) (h0 : 0 < q) (h1 : 1 < q) : Fin q → Fin q :=
  fun a => if a = ⟨0, h0⟩ then ⟨1, h1⟩ else if a = ⟨1, h1⟩ then ⟨0, h0⟩ else a

theorem Potts.swapFn_c0 (q : Nat) (h0 : 0 < q) (h1 : 1 < q) :
    Potts.swapFn q h0 h1 ⟨0, h0⟩ = ⟨1, h1⟩ := if_pos rfl

theorem Potts.swapFn_c1 (q : Nat) (h0 : 0 < q) (h1 : 1 < q) :
    Potts.swapFn q h0 h1 ⟨1, h1⟩ = ⟨0, h0⟩ :=
  (if_neg (fin_zero_ne_one h0 h1).symm).trans (if_pos rfl)

theorem Potts.swapFn_other {q : Nat} {h0 : 0 < q} {h1 : 1 < q} {a : Fin q}
    (ha0 : a ≠ ⟨0, h0⟩) (ha1 : a ≠ ⟨1, h1⟩) :
    Potts.swapFn q h0 h1 a = a :=
  (if_neg ha0).trans (if_neg ha1)

/-- The colour swap is an involution. -/
theorem Potts.swapFn_invol (q : Nat) (h0 : 0 < q) (h1 : 1 < q) (a : Fin q) :
    Potts.swapFn q h0 h1 (Potts.swapFn q h0 h1 a) = a :=
  if ha0 : a = ⟨0, h0⟩ then
    let e1 : Potts.swapFn q h0 h1 a = ⟨1, h1⟩ :=
      (congrArg (Potts.swapFn q h0 h1) ha0).trans (Potts.swapFn_c0 q h0 h1)
    (congrArg (Potts.swapFn q h0 h1) e1).trans
      ((Potts.swapFn_c1 q h0 h1).trans ha0.symm)
  else if ha1 : a = ⟨1, h1⟩ then
    let e1 : Potts.swapFn q h0 h1 a = ⟨0, h0⟩ :=
      (congrArg (Potts.swapFn q h0 h1) ha1).trans (Potts.swapFn_c1 q h0 h1)
    (congrArg (Potts.swapFn q h0 h1) e1).trans
      ((Potts.swapFn_c0 q h0 h1).trans ha1.symm)
  else
    (congrArg (Potts.swapFn q h0 h1) (Potts.swapFn_other ha0 ha1)).trans
      (Potts.swapFn_other ha0 ha1)

/-- The colour transposition `(0 1)` as an element of `S_q`.  Its `toFun`
and `invFun` are the same involution, so both round-trip laws are
`Potts.swapFn_invol`. -/
def pottsSwap (q : Nat) (h0 : 0 < q) (h1 : 1 < q) : Perm q where
  toFun := Potts.swapFn q h0 h1
  invFun := Potts.swapFn q h0 h1
  left_inv := Potts.swapFn_invol q h0 h1
  right_inv := Potts.swapFn_invol q h0 h1

/-- The discrete-target choice rule used for the impossibility witness:
the identity on configurations, viewed into the discrete category.  It is
injective on objects, hence not constant on any non-trivial orbit. -/
def pottsDiscreteChoiceRule (n q : Nat) :
    PottsConfigCat n q ⥤ Discrete (PottsConfig n q) :=
  discreteFunctor (fun c => c)

/-- The transposition genuinely moves the all-colour-`0` configuration:
relabelling sends it to the all-colour-`1` configuration, which differs
at site `0`.  This is the non-orbit-constancy that obstructs aggregation. -/
theorem potts_action_moves_config (n q : Nat) (hn : 0 < n) (h0 : 0 < q) (h1 : 1 < q) :
    Potts.actOnConfig (pottsSwap q h0 h1) ((fun _ => ⟨0, h0⟩) : PottsConfig n q)
      ≠ ((fun _ => ⟨0, h0⟩) : PottsConfig n q) :=
  fun h =>
    let hsite : Potts.swapFn q h0 h1 ⟨0, h0⟩ = ⟨0, h0⟩ := congrFun h ⟨0, hn⟩
    fin_zero_ne_one h0 h1
      ((Potts.swapFn_c0 q h0 h1).symm.trans hsite).symm

/-- **Arrow-Impossibility regime witness (non-anonymous rule).**  The
identity discrete choice rule is not constant on `S_q`-orbits (the colour
transposition moves the all-`0` configuration), so by the contrapositive
of `lan_implies_orbit_constant` it admits no aggregation: it occupies the
Arrow-Impossibility regime, on the very same Potts action that realizes
the other two regimes. -/
theorem potts_arrow_impossibility_regime (n q : Nat) (hn : 0 < n) (hq : 1 < q) :
    IsArrowImpossibilityRegime (pottsConfigAction n q) (pottsDiscreteChoiceRule n q) :=
  fun ⟨L⟩ =>
    let h0 : 0 < q := Nat.lt_of_le_of_lt (Nat.zero_le 1) hq
    let g : Perm q := pottsSwap q h0 hq
    let x : PottsConfigCat n q := ⟨fun _ => ⟨0, h0⟩⟩
    let hconst :
        (pottsDiscreteChoiceRule n q).obj (((pottsConfigAction n q).act g).obj x)
          = (pottsDiscreteChoiceRule n q).obj x :=
      lan_implies_orbit_constant (pottsDiscreteChoiceRule n q) L g x
    potts_action_moves_config n q hn h0 hq (congrArg Discrete.val hconst)

/-! ## Capstone: the trichotomy stays intact and is inhabited for Potts -/

/-- **The trichotomy stays intact for the Potts action.**  The generic
exhaustiveness theorem, instantiated at the `S_q` Potts action: every
choice rule on the Potts configuration category lands in one of the three
regimes.  This is `Trichotomy.trichotomy` applied with `G := SymmetricGroup q`;
no new proof is needed, which is exactly the point. -/
theorem potts_trichotomy_holds {n q : Nat} {D : Type v} [Category.{v, v} D]
    (F : ChoiceRule (PottsConfigCat n q) D) :
    IsArrowDebreuRegime (pottsConfigAction n q) F ∨
    IsArrowImpossibilityRegime (pottsConfigAction n q) F ∨
    IsSchellingIsingRegime (pottsConfigAction n q) F :=
  trichotomy (pottsConfigAction n q) F

/-- **All three regimes are realized by the single Potts `Aggregation`
construction.**

1. Arrow-Impossibility: a non-anonymous discrete choice rule (`n ≥ 1`,
   `q ≥ 2`) occupies it.
2. Arrow-Debreu: the symmetric mean-field choice rule occupies it for
   every `β ≤ 1`.
3. Schelling-Ising: the same rule occupies it for every `β > 1` (`q ≥ 2`),
   via the `S_q`-orbit of ordered phases.

Read with `potts_trichotomy_holds`, this is the Potts generalization of
`trichotomy_regimes_realized`: three classical behaviours of one left Kan
extension along the orbit projection, now with the full permutation
symmetry `S_q` on `q`-ary spins rather than the binary `Z_2` flip. -/
theorem potts_trichotomy_regimes_realized :
    (∀ (n q : Nat), 0 < n → 1 < q →
        IsArrowImpossibilityRegime (pottsConfigAction n q) (pottsDiscreteChoiceRule n q)) ∧
    (∀ (n q : Nat) (β : Rat), β ≤ 1 →
        IsArrowDebreuRegime (pottsConfigAction n q) (pottsChoiceRule n q β)) ∧
    (∀ (n q : Nat) (β : Rat), 1 < q → 1 < β →
        IsSchellingIsingRegime (pottsConfigAction n q) (pottsChoiceRule n q β)) :=
  ⟨fun n q hn hq => potts_arrow_impossibility_regime n q hn hq,
   fun n q _β hβ => potts_disordered_arrow_debreu_regime n q hβ,
   fun n q _β hq hβ => potts_ordered_schelling_ising_regime n q hq hβ⟩

end UnifiedAggregation.Bridge
