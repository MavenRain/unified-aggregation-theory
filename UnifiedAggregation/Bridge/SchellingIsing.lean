/-
  UnifiedAggregation.Bridge.SchellingIsing

  Phase 1b foundations: the Schelling-Ising regime under the framework.

  The configuration space is a finite collection of spins indexed by
  `Fin n` (n sites or n agents).  The `Z_2` symmetry acts by flipping
  all spins simultaneously.  The ferromagnetic Ising Hamiltonian is
  `Z_2`-invariant, so any `Z_2`-equivariant choice rule respects this
  symmetry; spontaneous symmetry breaking corresponds to the Lan
  extension having multiple non-isomorphic selectors below the
  critical temperature `β_c`.

  This module lands the foundational pieces:
  - `Spin` (two-element type) with `flip` and the involution law
  - `SpinConfig n` = `Fin n → Spin` with pointwise `flip`
  - The `Z_2` action on `Spin` and `SpinConfig n`
  - `SpinConfigCat n` = discrete category on spin configurations
  - `spinConfigAction` : `GAction Z2Group (SpinConfigCat n)`

  The bifurcation theorem (universal cocone of `Lan_p F_β` has one
  component for `β < β_c` and two for `β > β_c`) is stated with sorry;
  its proof requires real-valued machinery (Boltzmann weights, the
  mean-field magnetization equation, fixed-point analysis) outside the
  scope of this commit.
-/

import UnifiedAggregation.Discrete
import UnifiedAggregation.Z2Group
import UnifiedAggregation.Aggregation
import UnifiedAggregation.Regimes
import UnifiedAggregation.FunctorExt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

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

`act_one` closes by the same `Functor.ext` recipe as `profileAction`
(funext + rfl + heq_of_eq + match on `DiscreteHom.id`).

`act_mul` case-splits on `(x, y)`:
- `(.e, _)`, `(.g, .e)`: composition is definitional, same recipe.
- `(.g, .g)`: sorried.  Here the obj fields are propositionally but
  not definitionally equal:
    LHS.obj X = ⟨X.val⟩  (after reducing actOnConfig .e)
    RHS.obj X = ⟨X.val.flip.flip⟩  (double flip)
  The equality `X.val.flip.flip = X.val` is `SpinConfig.flip_flip`,
  applied componentwise on `Fin n → Spin` via funext.  This is the
  same fundamental obstacle as the orbit-groupoid cast-tower HEqs in
  `Aggregation.lean`: `Functor.ext`'s HEq on the `map` field needs
  the obj fields definitionally equal to apply `heq_of_eq` after a
  funext + match-on-`DiscreteHom.id` proof.  Resolving needs either:
  - an HEq-aware Functor extensionality lemma that handles
    obj-equal-up-to-funext, or
  - a custom transport through the involution.

Tracked alongside the Aggregation HEq sorries as a common technical
obstruction.  The structural construction is in place; the law for
`.g, .g` is the only remaining gap. -/
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

The minimality claim (these are the *ground states*) needs the
magnetization bound `|M(c)| ≤ n`, which is provable by induction on
`n` but is deferred — the Z₂-degeneracy claim alone is the
load-bearing piece for symmetry-breaking. -/
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

/-- For `β ≤ 1` (paramagnetic phase), `m = 0` is the unique
mean-field fixed point.

Proof sketch (deferred): the function `f(m) = tanh(β · m) - m` has
`f'(m) = β · sech²(β m) - 1 = β / cosh²(β m) - 1`.  For `β ≤ 1` and
`m ≠ 0`, `cosh²(β m) > 1`, so `f'(m) < 0`.  Combined with `f(0) = 0`
this gives `f(m) ≠ 0` for `m ≠ 0`, hence uniqueness. -/
theorem unique_fixed_point_paramagnetic (β : ℝ) (_hβ : β ≤ 1) :
    ∀ m : ℝ, IsMeanFieldFixedPoint β m → m = 0 := by sorry

/-- For `β > 1` (ferromagnetic phase), there exist two distinct
non-zero mean-field fixed points (the `Z₂`-symmetric attractor pair).

Proof sketch (deferred): consider `g(m) = tanh(β · m)`.  At `m = 0`,
`g'(0) = β > 1`, so `g` crosses the diagonal `y = m` with slope `> 1`
near zero.  Since `g` is bounded by `±1` and odd, `g(m) - m` changes
sign in `(0, 1)` and in `(-1, 0)` by the intermediate value theorem,
yielding two symmetric non-zero solutions. -/
theorem bifurcation_ferromagnetic (β : ℝ) (_hβ : 1 < β) :
    ∃ m₁ m₂ : ℝ, m₁ ≠ m₂ ∧ m₁ ≠ 0 ∧ m₂ ≠ 0 ∧
      IsMeanFieldFixedPoint β m₁ ∧ IsMeanFieldFixedPoint β m₂ := by sorry

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
