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
- `(.g, .g)`: needs `SpinConfig.flip_flip` to align the obj fields.
  This case is sorried — it requires either an HEq-aware Functor.ext
  variant or a custom transport through the flip-involution.
  Tracked as Phase 1b follow-up. -/
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
    | .g, .g => sorry

/-! ## Bifurcation theorem (statement)

The Schelling-Ising headline: for the `Z_2` action on spin
configurations and the Brock-Durlauf β-family of logit choice rules,
the universal cocone of `Lan_p F_β` has one connected component for
`β < β_c` and two for `β > β_c`.

The proof requires real-valued machinery (Boltzmann distribution,
mean-field magnetization equation, fixed-point analysis) that is the
Phase 1b deliverable.  Stated here with sorry as a long-term target. -/
theorem schelling_ising_bifurcation
    {n : Nat} {D : Type} [Category.{0, 0} D]
    {β : Type} (F : β → ChoiceRule (SpinConfigCat n) D)
    (β_c : β) :
    -- statement placeholder: existence of a bifurcation parameter
    -- separating uniqueness from multi-stability
    True := by sorry

end UnifiedAggregation.Bridge
