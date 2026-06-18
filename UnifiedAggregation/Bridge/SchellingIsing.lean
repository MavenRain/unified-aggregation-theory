/-
  UnifiedAggregation.Bridge.SchellingIsing

  The Schelling-Ising regime under the framework.

  The configuration space is a finite collection of spins indexed by
  `Fin n` (n sites or n agents).  The `Z_2` symmetry acts by flipping
  all spins simultaneously.  The ferromagnetic Ising Hamiltonian is
  `Z_2`-invariant, so any `Z_2`-equivariant choice rule respects this
  symmetry; spontaneous symmetry breaking corresponds to the Lan
  extension having multiple non-isomorphic selectors above the
  critical temperature `β_c = 1`.

  This module ships:

  Categorical embedding:
  - `Spin` (two-element type) with `flip` and the involution law
  - `SpinConfig n` = `Fin n → Spin` with pointwise `flip`
  - The `Z_2` action on `Spin` and `SpinConfig n`
  - `SpinConfigCat n` = discrete category on spin configurations
  - `spinConfigAction : GAction Z2Group (SpinConfigCat n)`

  Symbolic bifurcation theorem (Int-level):
  - `Magnetization`, `Hamiltonian`, and their `Z_2` symmetry laws
    (`Magnetization_flip`, `Hamiltonian_flip`)
  - `schelling_ising_z2_degeneracy`: for `n ≥ 1` the Hamiltonian
    admits at least two distinct configurations with equal energy

  Analytic bifurcation theorem (rational-valued, Mathlib-free):
  - `IsMeanFieldFixedPoint β m := m * (1 + |β·m|) = β·m`  (the
    denominator-cleared rational algebraic sigmoid `r(x) = x/(1+|x|)`,
    in place of `Real.tanh`; same pitchfork, rational fixed points)
  - `unique_fixed_point_paramagnetic` (`β ≤ 1`: only `m = 0`)
  - `bifurcation_ferromagnetic` (`β > 1`: the pair `±(β-1)/β`)
  - `mean_field_bifurcation` packaging both ends

  All theorems are sorry-free, and the whole module is **Mathlib-free**:
  the symbolic (Int-level) half uses kan-tactics + term mode; the analytic
  half uses core `Rat` field lemmas (term mode) and `kan_saturate` (the
  Mathlib-free ordered-field / `linarith`-over-`Rat` leg of
  `kan-saturation`) for the linear-arithmetic steps.  Arithmetic facts
  that depend on a hypothesis are factored into small parameterized helper
  lemmas, because `kan_saturate` reads only lambda/parameter-bound
  hypotheses (not ones introduced by `kan_by_cases`).
-/

import KanTactics
import UnifiedAggregation.Discrete
import UnifiedAggregation.Z2Group
import UnifiedAggregation.FunctorExt
import UnifiedAggregation.Aggregation
import UnifiedAggregation.Regimes
import UnifiedAggregation.Indiscrete
import KanSaturation

set_option autoImplicit false

namespace UnifiedAggregation.Bridge

open CompCatTheory

/-- Mathlib-free `congrArg₂` (the generic one lives in Mathlib). -/
private theorem congrArg₂ {α β γ : Sort _} (f : α → β → γ) {a₁ a₂ : α} {b₁ b₂ : β}
    (h₁ : a₁ = a₂) (h₂ : b₁ = b₂) : f a₁ b₁ = f a₂ b₂ :=
  (congrArg (f a₁) h₂).trans (congrArg (f · b₂) h₁)

/-! ## Spins and the Z₂ flip -/

/-- An Ising spin, taking one of two values.  `up` represents +1 and
`down` represents -1 in the usual notation. -/
inductive Spin where
  | up
  | down
  deriving DecidableEq

/-- Spin flip: `up ↔ down`. -/
def Spin.flip : Spin → Spin
  | .up => .down
  | .down => .up

/-- Flip is an involution. -/
theorem Spin.flip_flip : ∀ s : Spin, s.flip.flip = s
  | .up => rfl
  | .down => rfl

/-- `Z_2` acts on spins: `e` by identity, `g` by flip. -/
def Z2.actOnSpin : Z2 → Spin → Spin
  | .e, s => s
  | .g, s => s.flip

/-- The identity element acts as identity on spins. -/
theorem Z2.actOnSpin_one : ∀ s : Spin, Z2.actOnSpin .e s = s :=
  fun _ => rfl

/-- The action respects group multiplication.  Cases on `(x, y)`:
- `e _`: identity left, trivial.
- `g e`: identity right, trivial.
- `g g`: `actOnSpin (g·g) s = actOnSpin e s = s`, while
        `actOnSpin g (actOnSpin g s) = s.flip.flip = s` by `Spin.flip_flip`. -/
theorem Z2.actOnSpin_mul : ∀ x y : Z2, ∀ s : Spin,
    Z2.actOnSpin (Z2.mul x y) s = Z2.actOnSpin x (Z2.actOnSpin y s)
  | .e, _, _ => rfl
  | .g, .e, _ => rfl
  | .g, .g, s => (Spin.flip_flip s).symm

/-! ## Spin configurations and the pointwise flip -/

/-- A configuration of `n` spins on sites indexed by `Fin n`. -/
def SpinConfig (n : Nat) : Type := Fin n → Spin

/-- Pointwise flip on a spin configuration. -/
def SpinConfig.flip {n : Nat} (c : SpinConfig n) : SpinConfig n :=
  fun i => (c i).flip

/-- Pointwise flip is an involution on configurations. -/
theorem SpinConfig.flip_flip {n : Nat} (c : SpinConfig n) :
    c.flip.flip = c :=
  funext fun i => Spin.flip_flip (c i)

/-- `Z_2` acts on spin configurations pointwise. -/
def Z2.actOnConfig {n : Nat} : Z2 → SpinConfig n → SpinConfig n
  | .e, c => c
  | .g, c => c.flip

/-- The identity element acts as identity on configurations. -/
theorem Z2.actOnConfig_one {n : Nat} :
    ∀ c : SpinConfig n, Z2.actOnConfig .e c = c :=
  fun _ => rfl

/-- The action respects group multiplication on configurations. -/
theorem Z2.actOnConfig_mul {n : Nat} :
    ∀ x y : Z2, ∀ c : SpinConfig n,
      Z2.actOnConfig (Z2.mul x y) c
        = Z2.actOnConfig x (Z2.actOnConfig y c)
  | .e, _, _ => rfl
  | .g, .e, _ => rfl
  | .g, .g, c => (SpinConfig.flip_flip c).symm

/-! ## Categorical embedding: SpinConfigCat and the Z₂ action -/

/-- The configuration category for Schelling-Ising: discrete category
on spin configurations. -/
abbrev SpinConfigCat (n : Nat) : Type := Discrete (SpinConfig n)

/-- The endofunctor on `SpinConfigCat n` induced by a `Z_2` element.
Acts pointwise via `Z2.actOnConfig`. -/
def configActByZ2 {n : Nat} (z : Z2) :
    SpinConfigCat n ⥤ SpinConfigCat n :=
  discreteFunctor (Z2.actOnConfig z)

/-- Two discrete identity morphisms with propositionally-equal objects
are `HEq`.  The object equality `h : A = B` is a hypothesis with a free
variable on each side, so `kan_subst` aligns the two `id` types
definitionally, after which `HEq.rfl` closes.  Used for the `(.g, .g)`
case of `spinConfigAction.act_mul`, where the two functor `obj` fields
agree only up to `SpinConfig.flip_flip`. -/
private theorem heqDiscreteId {α : Type} {A B : Discrete α} (h : A = B) :
    HEq (DiscreteHom.id A) (DiscreteHom.id B) := by
  kan_subst h
  kan_exact HEq.rfl

/-- The `Z_2` action on `SpinConfig n` lifted to a `GAction` on
`SpinConfigCat n`.

`act_one` closes via the standard `Functor.ext` recipe (funext + rfl
+ heq_of_eq + match on `DiscreteHom.id`).

`act_mul` is more delicate: in the `(.flip, .flip)` case the
composed action's `obj` field is
`⟨X.val.flip.flip⟩` while the identity action's `obj` field is
`⟨X.val⟩`.  These are propositionally but not definitionally equal,
with the equality witnessed pointwise by `SpinConfig.flip_flip`
under a funext.  `Functor.ext` cannot apply directly here because
its `HEq` on the `map` field requires the `obj` fields to be
definitionally equal.

`UnifiedAggregation.FunctorExt.Functor.ext_pointwise` closes this
case: it consumes a pointwise obj-equality (built via funext +
`flip_flip` on each `Spin`) and discharges the `map` HEq, after
matching the single `.id` morphism, through the `kan_subst`-based
`heqDiscreteId` helper. -/
def spinConfigAction (n : Nat) :
    GAction Z2Group (SpinConfigCat n) where
  act := configActByZ2
  act_one :=
    UnifiedAggregation.Functor.ext
      (funext (fun _ => rfl))
      (heq_of_eq (funext (fun _ => funext (fun _ => funext (fun h =>
        match h with
        | DiscreteHom.id _ => rfl)))))
  act_mul x y :=
    match x, y with
    | .e, _ =>
      UnifiedAggregation.Functor.ext (funext (fun _ => rfl))
        (heq_of_eq (funext (fun _ => funext (fun _ => funext (fun h =>
          match h with
          | DiscreteHom.id _ => rfl)))))
    | .g, .e =>
      UnifiedAggregation.Functor.ext (funext (fun _ => rfl))
        (heq_of_eq (funext (fun _ => funext (fun _ => funext (fun h =>
          match h with
          | DiscreteHom.id _ => rfl)))))
    | .g, .g =>
      -- obj fields differ by `flip_flip` (propositional, not definitional),
      -- so route through pointwise extensionality; the single `.id`
      -- morphism's `HEq` follows from the object equality via the
      -- `kan_subst`-based `heqDiscreteId` helper.
      UnifiedAggregation.Functor.ext_pointwise _ _
        (fun X => congrArg Discrete.mk (SpinConfig.flip_flip X.val).symm)
        (fun {X _Y} h =>
          match h with
          | DiscreteHom.id _ =>
            heqDiscreteId (congrArg Discrete.mk (SpinConfig.flip_flip X.val).symm))

/-! ## Bifurcation machinery — magnetization (order parameter)

The order parameter for ferromagnetic Ising is the magnetization:
the signed count of up-spins minus down-spins, normalized by
configuration size.  Here we work with the un-normalized integer
magnetization for clean recursive definitions; normalization to a
rational/real magnetization can be layered on top.

The key Z₂ symmetry property: flipping all spins negates the
magnetization.  This is what makes `m = 0` the symmetric fixed
point of any Z₂-equivariant dynamics, and what makes bifurcation
to nonzero `±m_*` a genuine symmetry-breaking event. -/

/-- Signed value of a single spin: `+1` for up, `-1` for down. -/
def spinValue : Spin → Int
  | .up => 1
  | .down => -1

/-- Flipping a spin negates its signed value. -/
theorem spinValue_flip : ∀ s : Spin, spinValue s.flip = -spinValue s
  | .up => rfl
  | .down => rfl

/-- Sum of signed spin values over a configuration, defined by
recursion on `n` peeling off the last index via `Fin.last` and
recursing on the remaining `Fin k`-indexed restriction via
`Fin.castSucc`. -/
def sumSpinValues : (n : Nat) → SpinConfig n → Int
  | 0, _ => 0
  | k + 1, c =>
    spinValue (c (Fin.last k))
      + sumSpinValues k (fun i => c (Fin.castSucc i))

/-- Magnetization: the signed count of up-spins minus down-spins
for a spin configuration of size `n`. -/
def Magnetization {n : Nat} (c : SpinConfig n) : Int :=
  sumSpinValues n c

/-- **Z₂ inversion of magnetization**: flipping all spins negates the
magnetization.  This is the key symmetry that drives spontaneous
symmetry breaking in Ising — `m = 0` is the unique symmetric fixed
point, and any nonzero `m_*` comes in `Z₂`-related pairs `±m_*`.

Term-mode structural recursion on `n`: the last-index spin's flip
negates its signed value (`spinValue_flip`); the tail-restriction's
flip is the `SpinConfig.flip` of the restriction (definitional, so the
recursive call applies directly).  `congrArg₂ (·+·)` combines the two,
and `Int.neg_add.symm` folds `-a + -b` back into `-(a + b)`. -/
theorem Magnetization_flip : ∀ {n : Nat} (c : SpinConfig n),
    Magnetization c.flip = -Magnetization c
  | 0, _ => rfl
  | k + 1, c =>
    -- `M((k+1)-config) = sv(last) + M(tail)`; flip negates each summand
    -- (`spinValue_flip`, recursion on the tail) and `neg_add` folds the
    -- two negations back into one.  Pure term-mode structural recursion.
    (congrArg₂ (· + ·) (spinValue_flip (c (Fin.last k)))
        (Magnetization_flip (fun i => c (Fin.castSucc i)))).trans
      Int.neg_add.symm

/-! ## Hamiltonian (mean-field, integer-valued) -/

/-- The mean-field ferromagnetic Ising Hamiltonian on a spin
configuration, integer-valued (un-normalized by `n`):

  `H(c) = -(M(c))²`

This is the standard `-J Σᵢⱼ sᵢ sⱼ`-style energy specialized to the
mean-field approximation, with coupling `J = 1` and the `1/n`
normalization omitted (since we're staying in `Int`).  The
normalization can be added in a rational/real-valued layer above
this definition without changing any of the symmetry structure. -/
def Hamiltonian {n : Nat} (c : SpinConfig n) : Int :=
  -(Magnetization c * Magnetization c)

/-- **Z₂ invariance of the Hamiltonian**: flipping all spins leaves
the energy unchanged.  This is what makes the Boltzmann distribution
`exp(-β H)` `Z₂`-symmetric, and what forces any anonymous (= `Z₂`-
equivariant) choice rule based on the Hamiltonian to inherit the
symmetry.  Spontaneous symmetry breaking at low temperatures is then
a genuine "the dynamics has more symmetry than each individual
attractor" phenomenon.

Proved by chaining `Magnetization_flip` (which gives
`M(c.flip) = -M(c)`) with the standard `(-x)·(-x) = x·x` law via
`Int.neg_mul`, `Int.mul_neg`, `Int.neg_neg`. -/
theorem Hamiltonian_flip {n : Nat} (c : SpinConfig n) :
    Hamiltonian c.flip = Hamiltonian c :=
  -- `H = -(M·M)`; `M(flip) = -M` and `(-M)·(-M) = M·M` (`neg_mul_neg`),
  -- so the energy is invariant.  Term mode (`unfold` would force the
  -- `Magnetization` defn open, which `kan_dsimp` cannot scope).
  (congrArg (fun z => -(z * z)) (Magnetization_flip c)).trans
    (congrArg Neg.neg (Int.neg_mul_neg (Magnetization c) (Magnetization c)))

/-! ## Ground states: upConfig and downConfig -/

/-- The all-up spin configuration. -/
def upConfig (n : Nat) : SpinConfig n := fun _ => .up

/-- The all-down spin configuration. -/
def downConfig (n : Nat) : SpinConfig n := fun _ => .down

/-- Flipping `upConfig` gives `downConfig` (Z₂-related ground states). -/
theorem upConfig_flip (n : Nat) : (upConfig n).flip = downConfig n :=
  funext fun _ => rfl

/-- Flipping `downConfig` gives `upConfig`. -/
theorem downConfig_flip (n : Nat) : (downConfig n).flip = upConfig n :=
  funext fun _ => rfl

/-- For `n ≥ 1`, `upConfig` and `downConfig` are distinct configurations. -/
theorem upConfig_ne_downConfig {n : Nat} (hn : 0 < n) :
    upConfig n ≠ downConfig n :=
  fun h => Spin.noConfusion (congrFun h ⟨0, hn⟩)

/-- Magnetization of `upConfig` is `+n`. -/
theorem Magnetization_upConfig : ∀ (n : Nat),
    Magnetization (upConfig n) = (n : Int)
  | 0 => rfl
  | k + 1 =>
    -- `M(up_{k+1}) = 1 + M(up_k) = 1 + k = (k+1)`.  Term-mode recursion;
    -- the cast identity replaces the original `omega`.
    (congrArg (1 + ·) (Magnetization_upConfig k)).trans
      ((Int.add_comm 1 (k : Int)).trans (Int.natCast_succ k).symm)

/-- Magnetization of `downConfig` is `-n`, by Z₂ inversion. -/
theorem Magnetization_downConfig (n : Nat) :
    Magnetization (downConfig n) = -(n : Int) := by
  kan_rw [<- upConfig_flip n, Magnetization_flip (upConfig n), Magnetization_upConfig n]

/-! ## Bifurcation theorem (symbolic Z₂ degeneracy)

The Schelling-Ising headline at the level of ground-state structure:
flipping all spins preserves the energy, so any minimum-energy
configuration has a Z₂-paired sibling.  Concretely, `upConfig` and
`downConfig` are distinct configurations with equal Hamiltonian.

The full analytic bifurcation theorem (universal cocone of `Lan_p F_β`
has one component for β < β_c, two for β > β_c) requires Boltzmann
weights, mean-field magnetization equation, and fixed-point analysis
— all real-valued machinery beyond the Int-level scope of this
foundation.  The symbolic Z₂ degeneracy below captures the
*structural* content of bifurcation: distinct configurations
achieving the same minimum energy, witnessing the symmetry-breaking
attractor pairing. -/

/-- **Symbolic Z₂ bifurcation**: for `n ≥ 1`, the Schelling-Ising
Hamiltonian admits at least two distinct configurations with equal
energy, namely `upConfig n` and `downConfig n`.

A sharper minimality claim (that these are the *ground states*, via
the magnetization bound `|M(c)| ≤ n`) is left as a downstream
extension; the Z₂-degeneracy claim alone is the load-bearing piece
for symmetry-breaking. -/
theorem schelling_ising_z2_degeneracy {n : Nat} (hn : 0 < n) :
    ∃ c₁ c₂ : SpinConfig n,
      c₁ ≠ c₂ ∧ Hamiltonian c₁ = Hamiltonian c₂ := by
  kan_refine ⟨upConfig n, downConfig n, ?_, ?_⟩
  · kan_exact upConfig_ne_downConfig hn
  · kan_rw [<- upConfig_flip n, Hamiltonian_flip (upConfig n)]

/-! ## Bifurcation theorem (analytic, rational-valued)

Mathlib-free replacement for the `Real.tanh` development.  The mean-field
self-consistency uses the rational algebraic sigmoid `r(x) = x / (1 + |x|)`
in place of `tanh`: the same odd, slope-`β`-at-`0`, saturating shape, but
with the symmetry-broken fixed points `±(β-1)/β` *rational*, so the entire
development lives in `Rat`.  Each obligation is discharged by core `Rat`
field lemmas (term mode) or the Mathlib-free `kan_saturate` (ordered-field
leg).  Arithmetic facts depending on a hypothesis are factored into small
parameterized helper lemmas, since `kan_saturate` reads only
lambda/parameter-bound hypotheses, not ones introduced by `kan_by_cases`. -/


private theorem rat_neg_nonneg {q : Rat} (h : q < 0) : (0:Rat) ≤ -q := by kan_saturate
private theorem rat_negneg (q : Rat) : - -q = q := by kan_saturate
private theorem rat_eq_both_nonneg {q : Rat} (h1 : 0 ≤ q) (h2 : 0 ≤ -q) : -q = q := by kan_saturate
private theorem rat_sub_one_nonneg {β : Rat} (h : 1 < β) : (0:Rat) ≤ β - 1 := by kan_saturate
private theorem rat_one_add_sub_one (β : Rat) : (1:Rat) + (β - 1) = β := by kan_saturate
private theorem rat_pos_ne_zero {β : Rat} (h : 1 < β) : β ≠ 0 := fun h0 => by kan_saturate
private theorem rat_sub_one_ne {β : Rat} (h : 1 < β) : β - 1 ≠ 0 := fun hz => by kan_saturate
private theorem rat_paramag_zero {R β : Rat} (hc : 1 + R = β) (hn : 0 ≤ R) (hb : β ≤ 1) : R = 0 := by kan_saturate
private theorem rat_beta_eq_one {R β : Rat} (hc : 1 + R = β) (h0 : R = 0) : β = 1 := by kan_saturate
private theorem rat_neg_eq_zero {x : Rat} (h : -x = 0) : x = 0 := by kan_saturate
private theorem rat_neg_ne {x : Rat} (h : x ≠ 0) : -x ≠ 0 := fun h0 => h (rat_neg_eq_zero h0)
private theorem rat_ne_neg_self {x : Rat} (h : x ≠ 0) : x ≠ -x := fun he => h (by kan_saturate)

def ratAbs (q : Rat) : Rat := if q < 0 then -q else q
theorem ratAbs_of_neg {q : Rat} (h : q < 0) : ratAbs q = -q := if_pos h
theorem ratAbs_of_nonneg {q : Rat} (h : 0 ≤ q) : ratAbs q = q := if_neg (Rat.not_lt.mpr h)

theorem ratAbs_nonneg (q : Rat) : 0 ≤ ratAbs q := by
  kan_by_cases h : q < 0
  · kan_rw [ratAbs_of_neg h]; kan_exact rat_neg_nonneg h
  · kan_rw [ratAbs_of_nonneg (Rat.not_lt.mp h)]; kan_exact Rat.not_lt.mp h

theorem ratAbs_neg (q : Rat) : ratAbs (-q) = ratAbs q := by
  kan_by_cases h : q < 0
  · kan_rw [ratAbs_of_nonneg (rat_neg_nonneg h), ratAbs_of_neg h]
  · kan_by_cases h2 : -q < 0
    · kan_rw [ratAbs_of_neg h2, ratAbs_of_nonneg (Rat.not_lt.mp h)]
      kan_exact rat_negneg q
    · kan_rw [ratAbs_of_nonneg (Rat.not_lt.mp h2), ratAbs_of_nonneg (Rat.not_lt.mp h)]
      kan_exact rat_eq_both_nonneg (Rat.not_lt.mp h) (Rat.not_lt.mp h2)

theorem ratAbs_eq_zero {q : Rat} (h : ratAbs q = 0) : q = 0 := by
  kan_by_cases hq : q < 0
  · kan_exact rat_neg_eq_zero ((ratAbs_of_neg hq).symm.trans h)
  · kan_exact (ratAbs_of_nonneg (Rat.not_lt.mp hq)).symm.trans h

theorem ratMulLeftCancel {a b c : Rat} (ha : a ≠ 0) (h : a * b = a * c) : b = c :=
  have e : a⁻¹ * (a * b) = a⁻¹ * (a * c) := congrArg (a⁻¹ * ·) h
  have lhs : a⁻¹ * (a * b) = b := by
    kan_rw [<- Rat.mul_assoc a⁻¹ a b, Rat.inv_mul_cancel a ha, Rat.one_mul b]
  have rhs : a⁻¹ * (a * c) = c := by
    kan_rw [<- Rat.mul_assoc a⁻¹ a c, Rat.inv_mul_cancel a ha, Rat.one_mul c]
  lhs.symm.trans (e.trans rhs)

def IsMeanFieldFixedPoint (β m : Rat) : Prop := m * (1 + ratAbs (β * m)) = β * m

theorem zero_is_fixed_point (β : Rat) : IsMeanFieldFixedPoint β 0 :=
  (Rat.zero_mul _).trans (Rat.mul_zero β).symm

theorem unique_fixed_point_paramagnetic (β : Rat) (hβ : β ≤ 1) :
    ∀ m : Rat, IsMeanFieldFixedPoint β m → m = 0 := by
  kan_intros m h
  kan_by_cases hm : m = 0
  · kan_exact hm
  · have h2 : m * (1 + ratAbs (β * m)) = m * β := h.trans (Rat.mul_comm β m)
    have hcanc : 1 + ratAbs (β * m) = β := ratMulLeftCancel hm h2
    have hR0 : ratAbs (β * m) = 0 := rat_paramag_zero hcanc (ratAbs_nonneg (β * m)) hβ
    have hβm0 : β * m = 0 := ratAbs_eq_zero hR0
    have hβ1 : β = 1 := rat_beta_eq_one hcanc hR0
    have hmβ : m = β * m := by kan_rw [hβ1, Rat.one_mul m]
    kan_exact hmβ.trans hβm0

theorem mffp_pos {β : Rat} (hβ : 1 < β) : IsMeanFieldFixedPoint β ((β - 1) / β) := by
  have hβm : β * ((β - 1) / β) = β - 1 := by
    kan_rw [Rat.div_def (β - 1) β, Rat.mul_comm (β - 1) β⁻¹, <- Rat.mul_assoc β β⁻¹ (β - 1),
            Rat.mul_inv_cancel β (rat_pos_ne_zero hβ), Rat.one_mul (β - 1)]
  have hmβ : ((β - 1) / β) * β = β - 1 := by
    kan_rw [Rat.div_def (β - 1) β, Rat.mul_assoc (β - 1) β⁻¹ β,
            Rat.inv_mul_cancel β (rat_pos_ne_zero hβ), Rat.mul_one (β - 1)]
  have habs : ratAbs (β * ((β - 1) / β)) = β - 1 := by
    kan_rw [hβm, ratAbs_of_nonneg (rat_sub_one_nonneg hβ)]
  show ((β - 1) / β) * (1 + ratAbs (β * ((β - 1) / β))) = β * ((β - 1) / β)
  kan_rw [habs, rat_one_add_sub_one β, hmβ, hβm]

theorem mffp_neg_of {β m : Rat} (h : IsMeanFieldFixedPoint β m) :
    IsMeanFieldFixedPoint β (-m) := by
  have heven : ratAbs (β * -m) = ratAbs (β * m) := by
    kan_rw [Rat.mul_neg β m, ratAbs_neg (β * m)]
  show (-m) * (1 + ratAbs (β * -m)) = β * -m
  kan_rw [heven, Rat.mul_neg β m, Rat.neg_mul m (1 + ratAbs (β * m))]
  kan_exact congrArg Neg.neg h

theorem bifurcation_ferromagnetic (β : Rat) (hβ : 1 < β) :
    ∃ m₁ m₂ : Rat, m₁ ≠ m₂ ∧ m₁ ≠ 0 ∧ m₂ ≠ 0 ∧
      IsMeanFieldFixedPoint β m₁ ∧ IsMeanFieldFixedPoint β m₂ := by
  have hmβ : ((β - 1) / β) * β = β - 1 := by
    kan_rw [Rat.div_def (β - 1) β, Rat.mul_assoc (β - 1) β⁻¹ β,
            Rat.inv_mul_cancel β (rat_pos_ne_zero hβ), Rat.mul_one (β - 1)]
  have hne1 : (β - 1) / β ≠ 0 := fun h0 =>
    rat_sub_one_ne hβ (by kan_rw [<- hmβ, h0, Rat.zero_mul β])
  kan_exact ⟨(β - 1) / β, -((β - 1) / β), rat_ne_neg_self hne1, hne1,
            rat_neg_ne hne1, mffp_pos hβ, mffp_neg_of (mffp_pos hβ)⟩


/-- **The mean-field bifurcation theorem** (rational form): unique fixed
point `m = 0` for `β ≤ 1`, a symmetry-broken pair for `β > 1`; pitchfork at
`β_c = 1`.  Mathlib-free (core `Rat` + `kan_saturate`). -/
theorem mean_field_bifurcation :
    (∀ β : Rat, β ≤ 1 → ∀ m : Rat, IsMeanFieldFixedPoint β m → m = 0) ∧
    (∀ β : Rat, 1 < β → ∃ m₁ m₂ : Rat, m₁ ≠ m₂ ∧
       IsMeanFieldFixedPoint β m₁ ∧ IsMeanFieldFixedPoint β m₂) :=
  ⟨unique_fixed_point_paramagnetic,
   fun β hβ =>
     let ⟨m₁, m₂, h_ne, _, _, h₁, h₂⟩ := bifurcation_ferromagnetic β hβ
     ⟨m₁, m₂, h_ne, h₁, h₂⟩⟩


/-! ## Phase target and genuine regime witnesses (Phase 2)

The Int-level degeneracy and the analytic bifurcation above are real, but
live outside the categorical construction.  This section closes the gap:
the order-parameter target is the indiscrete groupoid on the *mean-field
fixed-point set*, so the cardinality of that set -- which
`mean_field_bifurcation` computes -- controls object-uniqueness of the
aggregation, hence the regime.  One phase (`m = 0`) for `β ≤ 1` gives the
Arrow-Debreu regime; the symmetry-broken pair `±m_*` for `β > 1` gives
the Schelling-Ising regime.  Both arise from the single `Aggregation`
construction (left Kan extension along the orbit projection of the `Z₂`
flip action) shared with the Arrow-Impossibility witness. -/

/-- The **phase category** at inverse temperature `β`: the indiscrete
groupoid on the set of mean-field fixed points.  Objects are the
order-parameter values the system can settle into; the unique morphism
between any two encodes their physical equivalence under the `Z₂` flip.
The number of objects is the number of fixed points, which bifurcates at
`β_c = 1`. -/
abbrev MagPhase (β : Rat) : Type :=
  Indiscrete {m : Rat // IsMeanFieldFixedPoint β m}

/-- The symmetric (paramagnetic) reference phase `m = 0`: a fixed point
at every `β` (`zero_is_fixed_point`). -/
def zeroPhase (β : Rat) : MagPhase β :=
  Indiscrete.mk ⟨0, zero_is_fixed_point β⟩

/-- The `Z₂`-symmetric choice rule sending every spin configuration to
the reference phase.  Spontaneous symmetry breaking is the statement
that, even though this rule is symmetric, its aggregation need not be
object-unique above `β_c`. -/
def magChoiceRule (n : Nat) (β : Rat) : SpinConfigCat n ⥤ MagPhase β :=
  constIndiscrete (zeroPhase β)

/-- For `β ≤ 1` the phase category is a subsingleton: every fixed point
is `m = 0` (`unique_fixed_point_paramagnetic`), so all objects of
`MagPhase β` are equal. -/
theorem magPhase_subsingleton {β : Rat} (hβ : β ≤ 1) :
    ∀ a b : MagPhase β, a = b :=
  fun a b =>
    congrArg Indiscrete.mk
      (Subtype.ext
        ((unique_fixed_point_paramagnetic β hβ a.val.val a.val.property).trans
          (unique_fixed_point_paramagnetic β hβ b.val.val b.val.property).symm))

/-- **Arrow-Debreu regime witness (paramagnetic phase, `β ≤ 1`).**  The
aggregation of the symmetric choice rule exists and is object-unique,
because the only fixed point is `m = 0`: the equilibrium order parameter
is uniquely determined.  Same `Aggregation` construction as every other
regime; the regime is forced by `unique_fixed_point_paramagnetic`. -/
theorem paramagnetic_arrow_debreu_regime (n : Nat) {β : Rat} (hβ : β ≤ 1) :
    IsArrowDebreuRegime (spinConfigAction n) (magChoiceRule n β) :=
  ⟨indiscreteLan (orbitProjection (spinConfigAction n)) (magChoiceRule n β)
      (zeroPhase β),
   fun _ _ => magPhase_subsingleton hβ _ _⟩

/-- **Schelling-Ising regime witness (ferromagnetic phase, `β > 1`).**
The aggregation of the *same* symmetric choice rule exists but is *not*
object-unique: the symmetry-broken pair `±m_*` from
`bifurcation_ferromagnetic` gives two distinct phases, hence two left
Kan extensions whose object-assignments differ.  Spontaneous symmetry
breaking realized as genuine non-uniqueness of the universal aggregate
-- impossible over a discrete target (see
`Characterization.not_schelling_ising_discrete`), which is exactly why
the phase groupoid is needed. -/
theorem schelling_ising_regime (n : Nat) {β : Rat} (hβ : 1 < β) :
    IsSchellingIsingRegime (spinConfigAction n) (magChoiceRule n β) :=
  match bifurcation_ferromagnetic β hβ with
  | ⟨m₁, m₂, hne, _, _, h₁, h₂⟩ =>
    ⟨indiscreteLan (orbitProjection (spinConfigAction n)) (magChoiceRule n β)
        (Indiscrete.mk ⟨m₁, h₁⟩),
     indiscreteLan (orbitProjection (spinConfigAction n)) (magChoiceRule n β)
        (Indiscrete.mk ⟨m₂, h₂⟩),
     ⟨⟨upConfig n⟩⟩,
     Indiscrete.mk_ne (fun h => hne (congrArg Subtype.val h))⟩

end UnifiedAggregation.Bridge
