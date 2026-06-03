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

  Analytic bifurcation theorem (Real-level, via Mathlib):
  - `IsMeanFieldFixedPoint β m := m = Real.tanh (β * m)`
  - `unique_fixed_point_paramagnetic` (`β ≤ 1`: only `m = 0`)
  - `bifurcation_ferromagnetic` (`β > 1`: a symmetry-broken pair)
  - `mean_field_bifurcation` packaging both ends

  All theorems are sorry-free; the analytic helpers use Mathlib
  tactics (`ring`, `linarith`, `nlinarith`, `field_simp`,
  `positivity`) as a documented exception to the kan-tactics
  convention.
-/

import UnifiedAggregation.Discrete
import UnifiedAggregation.Z2Group
import UnifiedAggregation.FunctorExt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Calculus.Deriv.MeanValue

set_option autoImplicit false

namespace UnifiedAggregation.Bridge

open CompCatTheory

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
`flip_flip` on each `Spin`) and routes the `map` HEq through a
`cases h`-and-rewrite pattern on the inferred motive. -/
def spinConfigAction (n : Nat) :
    GAction Z2Group (SpinConfigCat n) where
  act := configActByZ2
  act_one :=
    UnifiedAggregation.Functor.ext
      (funext (fun _ => rfl))
      (heq_of_eq (funext (fun _ => funext (fun _ => funext (fun h =>
        match h with
        | DiscreteHom.id _ => rfl)))))
  act_mul x y := by
    match x, y with
    | .e, _ =>
      exact UnifiedAggregation.Functor.ext (funext (fun _ => rfl))
        (heq_of_eq (funext (fun _ => funext (fun _ => funext (fun h =>
          match h with
          | DiscreteHom.id _ => rfl)))))
    | .g, .e =>
      exact UnifiedAggregation.Functor.ext (funext (fun _ => rfl))
        (heq_of_eq (funext (fun _ => funext (fun _ => funext (fun h =>
          match h with
          | DiscreteHom.id _ => rfl)))))
    | .g, .g =>
      apply UnifiedAggregation.Functor.ext_pointwise
      · -- pointwise obj equality: ⟨X.val⟩ = ⟨X.val.flip.flip⟩ via flip_flip
        intro X
        exact congrArg Discrete.mk (SpinConfig.flip_flip X.val).symm
      · -- pointwise map HEq.
        intro X Y h
        cases h
        show HEq (DiscreteHom.id (⟨X.val⟩ : SpinConfigCat n))
                 (DiscreteHom.id (⟨X.val.flip.flip⟩ : SpinConfigCat n))
        have h_obj_X : (⟨X.val.flip.flip⟩ : SpinConfigCat n) = ⟨X.val⟩ :=
          congrArg Discrete.mk (SpinConfig.flip_flip X.val)
        rw [h_obj_X]

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

Inductive proof on `n`: the last-index spin's flip negates its
signed value (`spinValue_flip`); the tail-restriction's flip is
the SpinConfig.flip of the restriction (rfl).  The arithmetic
identity `-a + -b = -(a + b)` closes by `omega`. -/
theorem Magnetization_flip {n : Nat} (c : SpinConfig n) :
    Magnetization c.flip = -Magnetization c := by
  induction n with
  | zero => rfl
  | succ k ih =>
    show spinValue (c.flip (Fin.last k))
          + sumSpinValues k (fun i => c.flip (Fin.castSucc i))
       = -(spinValue (c (Fin.last k))
          + sumSpinValues k (fun i => c (Fin.castSucc i)))
    have h_last : spinValue (c.flip (Fin.last k))
                  = -spinValue (c (Fin.last k)) := spinValue_flip _
    have h_tail_eq :
        (fun i : Fin k => c.flip (Fin.castSucc i))
          = SpinConfig.flip (fun i : Fin k => c (Fin.castSucc i)) := rfl
    have h_tail :
        sumSpinValues k (fun i : Fin k => c.flip (Fin.castSucc i))
          = -sumSpinValues k (fun i : Fin k => c (Fin.castSucc i)) := by
      rw [h_tail_eq]
      exact ih (fun i : Fin k => c (Fin.castSucc i))
    rw [h_last, h_tail]
    omega

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
    Hamiltonian c.flip = Hamiltonian c := by
  unfold Hamiltonian
  rw [Magnetization_flip, Int.neg_mul, Int.mul_neg, Int.neg_neg]

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
    upConfig n ≠ downConfig n := by
  intro h
  exact Spin.noConfusion (congrFun h ⟨0, hn⟩)

/-- Magnetization of `upConfig` is `+n`. -/
theorem Magnetization_upConfig (n : Nat) :
    Magnetization (upConfig n) = (n : Int) := by
  induction n with
  | zero => rfl
  | succ k ih =>
    show spinValue Spin.up
          + sumSpinValues k (fun _ : Fin k => Spin.up)
        = ((k + 1 : Nat) : Int)
    have h : sumSpinValues k (fun _ : Fin k => Spin.up) = (k : Int) := ih
    rw [h]
    show (1 : Int) + (k : Int) = ((k + 1 : Nat) : Int)
    omega

/-- Magnetization of `downConfig` is `-n`, by Z₂ inversion. -/
theorem Magnetization_downConfig (n : Nat) :
    Magnetization (downConfig n) = -(n : Int) := by
  rw [← upConfig_flip, Magnetization_flip, Magnetization_upConfig]

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
  refine ⟨upConfig n, downConfig n, ?_, ?_⟩
  · exact upConfig_ne_downConfig hn
  · rw [← upConfig_flip, Hamiltonian_flip]

/-! ## Bifurcation theorem (analytic, real-valued)

The classical mean-field bifurcation of the ferromagnetic Ising
model: the self-consistency equation `m = tanh(β · m)` has a single
fixed point `m = 0` for `β ≤ 1` (paramagnetic phase) and multiple
fixed points for `β > 1` (ferromagnetic phase with `Z₂`-broken
attractor pair `±m_*(β)` plus the unstable `m = 0`).

We use Mathlib's `Real.tanh` and standard real-analysis machinery. -/

/-- The mean-field self-consistency condition: `m` is a fixed point
of the magnetization equation `m = tanh(β · m)` (with coupling
`J = 1` so the critical inverse temperature is `β_c = 1`). -/
def IsMeanFieldFixedPoint (β m : ℝ) : Prop :=
  m = Real.tanh (β * m)

/-- Zero is always a mean-field fixed point: `0 = tanh(0)`. -/
theorem zero_is_fixed_point (β : ℝ) : IsMeanFieldFixedPoint β 0 := by
  unfold IsMeanFieldFixedPoint
  simp [Real.tanh_zero]

/-! ### Analytic helpers

The next two lemmas (`Real.tanh` strictly monotone, and
`Real.tanh x < x` for `x > 0`) are required for the paramagnetic
uniqueness proof but are not in Mathlib's `Real.tanh` API.  Both
are derived from the `Real.sinh` / `Real.cosh` machinery via
Mathlib tactics; this is a documented exception to the
kan-tactics-only convention since the proofs are real-analytic
identities for which kan-tactics has no equivalents. -/

/-- `Real.tanh` is strictly monotone.  Derived from
`Real.sinh_sub` and `Real.sinh_pos_iff` via the identity
`sinh y · cosh x - sinh x · cosh y = sinh(y - x)`. -/
theorem Real.tanh_strictMono : StrictMono Real.tanh := by
  intro x y hxy
  rw [Real.tanh_eq_sinh_div_cosh, Real.tanh_eq_sinh_div_cosh,
      div_lt_div_iff₀ (Real.cosh_pos x) (Real.cosh_pos y)]
  have h_sub : Real.sinh y * Real.cosh x - Real.sinh x * Real.cosh y
      = Real.sinh (y - x) := by
    rw [Real.sinh_sub]; ring
  have h_sinh_pos : 0 < Real.sinh (y - x) :=
    Real.sinh_pos_iff.mpr (sub_pos.mpr hxy)
  linarith

/-- For `x > 0`, `Real.tanh x < x`.  Proof: consider
`g(t) = t · cosh t - sinh t`.  Then `g(0) = 0` and
`g'(t) = t · sinh t > 0` for `t > 0`, so `g(x) > 0` for `x > 0`,
i.e., `sinh x < x · cosh x`, i.e., `tanh x < x`. -/
theorem Real.tanh_lt_self_of_pos {x : ℝ} (hx : 0 < x) :
    Real.tanh x < x := by
  suffices h : Real.sinh x < x * Real.cosh x by
    rw [Real.tanh_eq_sinh_div_cosh, div_lt_iff₀ (Real.cosh_pos x)]
    exact h
  -- g(t) = t · cosh t - sinh t.  g(0) = 0, g'(t) = t · sinh t > 0 for t > 0.
  have h_deriv : ∀ t, HasDerivAt (fun s => s * Real.cosh s - Real.sinh s)
                                  (t * Real.sinh t) t := by
    intro t
    have h₁ : HasDerivAt (fun s => s * Real.cosh s)
                          (1 * Real.cosh t + t * Real.sinh t) t :=
      (hasDerivAt_id t).mul (Real.hasDerivAt_cosh t)
    have h₂ : HasDerivAt Real.sinh (Real.cosh t) t := Real.hasDerivAt_sinh t
    convert h₁.sub h₂ using 1
    ring
  have h_mono : StrictMonoOn (fun s => s * Real.cosh s - Real.sinh s)
                              (Set.Ici 0) :=
    strictMonoOn_of_hasDerivWithinAt_pos (convex_Ici 0)
      (fun t _ => (h_deriv t).continuousAt.continuousWithinAt)
      (fun t _ => (h_deriv t).hasDerivWithinAt)
      (fun t ht => by
        have ht_pos : 0 < t := by
          simp only [interior_Ici, Set.mem_Ioi] at ht; exact ht
        exact mul_pos ht_pos (Real.sinh_pos_iff.mpr ht_pos))
  have h_zero : (fun s => s * Real.cosh s - Real.sinh s) 0 = 0 := by
    simp [Real.cosh_zero, Real.sinh_zero]
  have h_gt : 0 < x * Real.cosh x - Real.sinh x := by
    have := h_mono (Set.self_mem_Ici) (Set.mem_Ici.mpr hx.le) hx
    rw [h_zero] at this
    exact this
  linarith

/-- For `β ≤ 1` (paramagnetic phase), `m = 0` is the unique
mean-field fixed point.

Proof: assume `m = tanh(β·m)` with `m ≠ 0`.  WLOG `m > 0` (the
`m < 0` case follows by `Real.tanh_neg`).  Then `β·m ≤ m` (since
`β ≤ 1` and `m > 0`), so `tanh(β·m) ≤ tanh(m)` by monotonicity.
Combined with `m = tanh(β·m)` we get `m ≤ tanh(m)`.  But `m > 0`
implies `tanh(m) < m`, contradiction. -/
theorem unique_fixed_point_paramagnetic (β : ℝ) (hβ : β ≤ 1) :
    ∀ m : ℝ, IsMeanFieldFixedPoint β m → m = 0 := by
  intro m h
  unfold IsMeanFieldFixedPoint at h
  by_contra h_m_ne
  rcases lt_or_gt_of_ne h_m_ne with h_m_neg | h_m_pos
  · -- m < 0 case.
    have h_neg_pos : 0 < -m := neg_pos.mpr h_m_neg
    have h' : -m = Real.tanh (β * -m) := by
      rw [mul_neg, Real.tanh_neg, ← h]
    have h_le : β * -m ≤ -m := by
      rcases le_or_gt 0 β with hβ_pos | hβ_neg
      · calc β * -m
            ≤ 1 * -m := mul_le_mul_of_nonneg_right hβ h_neg_pos.le
          _ = -m := one_mul _
      · have h_np : β * -m < 0 := mul_neg_of_neg_of_pos hβ_neg h_neg_pos
        linarith
    have h_chain : -m ≤ Real.tanh (-m) :=
      h'.le.trans (Real.tanh_strictMono.monotone h_le)
    have h_lt : Real.tanh (-m) < -m := Real.tanh_lt_self_of_pos h_neg_pos
    linarith
  · -- m > 0 case.
    have h_le : β * m ≤ m := by
      rcases le_or_gt 0 β with hβ_pos | hβ_neg
      · calc β * m
            ≤ 1 * m := mul_le_mul_of_nonneg_right hβ h_m_pos.le
          _ = m := one_mul _
      · have h_np : β * m < 0 := mul_neg_of_neg_of_pos hβ_neg h_m_pos
        linarith
    have h_chain : m ≤ Real.tanh m :=
      h.le.trans (Real.tanh_strictMono.monotone h_le)
    have h_lt : Real.tanh m < m := Real.tanh_lt_self_of_pos h_m_pos
    linarith

/-- `Real.tanh` has derivative `1 / cosh²` at every real point.
Derived from `hasDerivAt_sinh` and `hasDerivAt_cosh` via the
quotient rule plus `cosh² - sinh² = 1`. -/
theorem Real.hasDerivAt_tanh (x : ℝ) :
    HasDerivAt Real.tanh (1 / Real.cosh x ^ 2) x := by
  have h := (Real.hasDerivAt_sinh x).div (Real.hasDerivAt_cosh x)
    (Real.cosh_pos x).ne'
  have h_fn : (Real.sinh / Real.cosh : ℝ → ℝ) = Real.tanh := by
    funext y
    exact (Real.tanh_eq_sinh_div_cosh y).symm
  rw [h_fn] at h
  have h_eq :
      (Real.cosh x * Real.cosh x - Real.sinh x * Real.sinh x) / Real.cosh x ^ 2
        = 1 / Real.cosh x ^ 2 := by
    have h_id := Real.cosh_sq_sub_sinh_sq x
    have : Real.cosh x * Real.cosh x - Real.sinh x * Real.sinh x = 1 := by
      have := h_id
      nlinarith [sq (Real.cosh x), sq (Real.sinh x)]
    rw [this]
  rw [h_eq] at h
  exact h

/-- For `y ∈ (0, 1)`, `Real.tanh y > y - y²`.  This is the auxiliary
inequality used in `bifurcation_ferromagnetic` to establish strict
positivity of `f(m) := tanh(β·m) - m` at the lower IVT endpoint
`m = (β-1)/β²` (where `β·m = (β-1)/β ∈ (0, 1)`).

Proof: define `g(t) := tanh t - t + t²`.  `g(0) = 0`,
`g'(t) = sech²(t) - 1 + 2t = -tanh²(t) + 2t`.  For `t ∈ (0, 1)`,
`tanh(t) < t` (via `Real.tanh_lt_self_of_pos`) so `tanh²(t) < t²`,
hence `g'(t) > 2t - t² = t(2 - t) > 0`.  By
`strictMonoOn_of_hasDerivWithinAt_pos`, `g` is strictly increasing
on `[0, 1]`, so `g(y) > g(0) = 0` for `y ∈ (0, 1]`. -/
theorem Real.tanh_gt_self_sub_sq {y : ℝ}
    (hy_pos : 0 < y) (hy_lt : y < 1) :
    y - y^2 < Real.tanh y := by
  -- Define g(t) := tanh t - t + t² and show strictMonoOn on [0, 1].
  have h_mono : StrictMonoOn (fun t : ℝ => Real.tanh t - t + t^2)
                              (Set.Icc 0 1) := by
    -- Derivative of g.
    have h_deriv : ∀ t,
        HasDerivAt (fun s : ℝ => Real.tanh s - s + s^2)
          (1 / Real.cosh t ^ 2 - 1 + 2 * t) t := by
      intro t
      have h_tanh := Real.hasDerivAt_tanh t
      have h_id : HasDerivAt (fun s : ℝ => s) 1 t := hasDerivAt_id t
      have h_sq : HasDerivAt (fun s : ℝ => s^2) (2 * t) t := by
        have := hasDerivAt_pow 2 t
        simp at this
        exact this
      exact (h_tanh.sub h_id).add h_sq
    refine strictMonoOn_of_hasDerivWithinAt_pos
      (f' := fun t => 1 / Real.cosh t ^ 2 - 1 + 2 * t)
      (convex_Icc 0 1) ?_ ?_ ?_
    · -- Continuity on [0, 1].
      intro t _
      exact ((h_deriv t).continuousAt).continuousWithinAt
    · -- Has derivative within the interior.
      intro t _
      exact (h_deriv t).hasDerivWithinAt
    · -- Derivative positive on the interior.
      intro t ht
      simp only [interior_Icc, Set.mem_Ioo] at ht
      obtain ⟨ht_pos, ht_lt⟩ := ht
      -- 1/cosh²(t) - 1 = -tanh²(t) ≥ -t²
      have h_tanh_lt : Real.tanh t < t := Real.tanh_lt_self_of_pos ht_pos
      have h_tanh_pos : 0 < Real.tanh t := by
        rw [Real.tanh_eq_sinh_div_cosh]
        exact div_pos (Real.sinh_pos_iff.mpr ht_pos) (Real.cosh_pos t)
      have h_tanh_sq : Real.tanh t ^ 2 < t ^ 2 := by
        have := mul_self_lt_mul_self h_tanh_pos.le h_tanh_lt
        rw [← sq, ← sq] at this
        exact this
      -- Key identity: 1/cosh²(t) = 1 - tanh²(t)
      have h_one_minus_tanh_sq : 1 / Real.cosh t ^ 2 = 1 - Real.tanh t ^ 2 := by
        rw [Real.tanh_eq_sinh_div_cosh, div_pow]
        field_simp
        linarith [Real.cosh_sq_sub_sinh_sq t]
      rw [h_one_minus_tanh_sq]
      nlinarith [h_tanh_sq]
  have h_zero : (fun t : ℝ => Real.tanh t - t + t^2) 0 = 0 := by
    simp [Real.tanh_zero]
  have h_0_in : (0 : ℝ) ∈ Set.Icc (0:ℝ) 1 := ⟨le_refl _, zero_le_one⟩
  have h_y_in : y ∈ Set.Icc (0:ℝ) 1 := ⟨hy_pos.le, hy_lt.le⟩
  have h_gt := h_mono h_0_in h_y_in hy_pos
  rw [h_zero] at h_gt
  linarith

/-- `Real.tanh` is continuous (as a quotient of continuous functions). -/
theorem Real.continuous_tanh : Continuous Real.tanh := by
  have h : Real.tanh = fun x => Real.sinh x / Real.cosh x := by
    funext x; exact Real.tanh_eq_sinh_div_cosh x
  rw [h]
  exact Real.continuous_sinh.div Real.continuous_cosh
    (fun x => (Real.cosh_pos x).ne')

/-- For `β > 1` (ferromagnetic phase), there exist two distinct
non-zero mean-field fixed points (the `Z₂`-symmetric attractor pair
`±m_*(β)`).

Proof: define `f(m) := tanh(β·m) - m` and `δ := (β-1)/β²`.  By
`Real.tanh_gt_self_sub_sq` at `y := (β-1)/β ∈ (0, 1)`, we get
`tanh((β-1)/β) > (β-1)/β² = δ`, hence `f(δ) > 0`.  Combined with
`f(1) = tanh β - 1 < 0` (`Real.tanh_lt_one`) and continuity, IVT
yields `m₁ ∈ [δ, 1]` with `f(m₁) = 0`.  By odd symmetry
(`Real.tanh_neg`), `-m₁` is also a fixed point. -/
theorem bifurcation_ferromagnetic (β : ℝ) (hβ : 1 < β) :
    ∃ m₁ m₂ : ℝ, m₁ ≠ m₂ ∧ m₁ ≠ 0 ∧ m₂ ≠ 0 ∧
      IsMeanFieldFixedPoint β m₁ ∧ IsMeanFieldFixedPoint β m₂ := by
  have hβ_pos : 0 < β := by linarith
  have hβ_sq_pos : 0 < β^2 := by positivity
  set δ : ℝ := (β - 1) / β^2 with hδ_def
  have hδ_pos : 0 < δ := div_pos (by linarith) hβ_sq_pos
  have hδ_lt_one : δ < 1 := by
    rw [hδ_def, div_lt_one hβ_sq_pos]
    nlinarith
  -- Lower-end positivity: tanh(β·δ) > δ.
  have h_lower : δ < Real.tanh (β * δ) := by
    have h_βδ : β * δ = (β - 1) / β := by
      rw [hδ_def]; field_simp
    rw [h_βδ]
    have h_y_pos : 0 < (β - 1) / β := div_pos (by linarith) hβ_pos
    have h_y_lt : (β - 1) / β < 1 := by
      rw [div_lt_one hβ_pos]; linarith
    have h_ineq := Real.tanh_gt_self_sub_sq h_y_pos h_y_lt
    have h_eq_δ : (β - 1) / β - ((β - 1) / β)^2 = δ := by
      rw [hδ_def]; field_simp; ring
    linarith [h_eq_δ.symm.trans_lt h_ineq]
  -- Continuity of the difference f(m) = tanh(β·m) - m.
  have h_f_cont : Continuous (fun m : ℝ => Real.tanh (β * m) - m) :=
    (Real.continuous_tanh.comp (continuous_const.mul continuous_id)).sub continuous_id
  -- IVT on [δ, 1] for f: f(δ) > 0, f(1) < 0, so f has a zero.
  have h_f_δ_pos : 0 < Real.tanh (β * δ) - δ := by linarith
  have h_f_one_neg : Real.tanh (β * 1) - 1 < 0 := by
    rw [mul_one]; linarith [Real.tanh_lt_one β]
  have h_δ_le : δ ≤ 1 := hδ_lt_one.le
  have h_in_range :
      (0 : ℝ) ∈ Set.Icc ((fun m => Real.tanh (β * m) - m) 1)
                        ((fun m => Real.tanh (β * m) - m) δ) := by
    refine ⟨?_, ?_⟩
    · show Real.tanh (β * 1) - 1 ≤ 0
      linarith [Real.tanh_lt_one β, show β * 1 = β from mul_one β]
    · show 0 ≤ Real.tanh (β * δ) - δ
      linarith
  obtain ⟨m₁, hm₁_mem, hm₁_eq⟩ :=
    intermediate_value_Icc' h_δ_le h_f_cont.continuousOn h_in_range
  -- m₁ ∈ [δ, 1] with f(m₁) = 0, i.e., tanh(β·m₁) = m₁.
  have hm₁_fp : IsMeanFieldFixedPoint β m₁ := by
    unfold IsMeanFieldFixedPoint
    have : Real.tanh (β * m₁) - m₁ = 0 := hm₁_eq
    linarith
  have hm₁_pos : 0 < m₁ := lt_of_lt_of_le hδ_pos hm₁_mem.1
  -- By odd symmetry, -m₁ is also a fixed point.
  have hm₂_fp : IsMeanFieldFixedPoint β (-m₁) := by
    unfold IsMeanFieldFixedPoint at hm₁_fp ⊢
    have h_t : Real.tanh (β * -m₁) = -Real.tanh (β * m₁) := by
      rw [mul_neg, Real.tanh_neg]
    rw [h_t, ← hm₁_fp]
  refine ⟨m₁, -m₁, ?_, ?_, ?_, hm₁_fp, hm₂_fp⟩
  · -- m₁ ≠ -m₁
    intro h
    nlinarith [hm₁_pos, h]
  · -- m₁ ≠ 0
    exact hm₁_pos.ne'
  · -- -m₁ ≠ 0
    intro h
    have : m₁ = 0 := by linarith
    exact hm₁_pos.ne' this

/-- **The mean-field bifurcation theorem**.  The number of solutions
of the self-consistency equation `m = tanh(β · m)` bifurcates at
`β_c = 1`: a unique solution `m = 0` for `β ≤ 1`, and multiple
distinct solutions (including the symmetry-broken pair `±m_*`) for
`β > 1`.

This is the analytic form of `schelling_ising_z2_degeneracy`: that
result captured the structural content (distinct configurations
with equal Hamiltonian) at the Int level; this captures the
real-valued phase-transition content at `β_c`. -/
theorem mean_field_bifurcation :
    (∀ β : ℝ, β ≤ 1 → ∀ m : ℝ, IsMeanFieldFixedPoint β m → m = 0) ∧
    (∀ β : ℝ, 1 < β → ∃ m₁ m₂ : ℝ, m₁ ≠ m₂ ∧
       IsMeanFieldFixedPoint β m₁ ∧ IsMeanFieldFixedPoint β m₂) :=
  ⟨unique_fixed_point_paramagnetic,
   fun β hβ =>
     let ⟨m₁, m₂, h_ne, _, _, h₁, h₂⟩ := bifurcation_ferromagnetic β hβ
     ⟨m₁, m₂, h_ne, h₁, h₂⟩⟩

end UnifiedAggregation.Bridge
