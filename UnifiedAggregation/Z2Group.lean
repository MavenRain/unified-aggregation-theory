/-
  UnifiedAggregation.Z2Group

  The cyclic group of order 2, Z_2 = {e, g} with g·g = e.  This is the
  Z_2 symmetry that governs Schelling-Ising under spin flip: g acts on
  a spin by negating it, and the Hamiltonian of the ferromagnetic
  Ising model is Z_2-invariant.

  Parallel construction to `SymmetricGroup`: an inductive carrier with
  three operations (id, mul, inv) and the five group laws proved in
  pure term mode by exhaustive case analysis.
-/

import UnifiedAggregation.ConfigSpace

set_option autoImplicit false

namespace UnifiedAggregation

/-- The cyclic group of order 2.  `e` is the identity element and `g`
is the non-identity generator (its own inverse, with `g · g = e`). -/
inductive Z2 where
  | e
  | g
  deriving DecidableEq

namespace Z2

/-- Multiplication in `Z_2`.  Defined by exhaustive case analysis: the
identity acts as expected on both sides, and `g · g = e`. -/
def mul : Z2 → Z2 → Z2
  | .e, x => x
  | .g, .e => .g
  | .g, .g => .e

/-- Inverse in `Z_2`.  Every element is its own inverse. -/
def inv : Z2 → Z2 := id

/-- `e` is a left identity. -/
theorem one_mul : ∀ x : Z2, mul .e x = x := fun _ => rfl

/-- `e` is a right identity. -/
theorem mul_one : ∀ x : Z2, mul x .e = x
  | .e => rfl
  | .g => rfl

/-- Multiplication is associative. -/
theorem mul_assoc : ∀ x y z : Z2, mul (mul x y) z = mul x (mul y z)
  | .e, _, _ => rfl
  | .g, .e, _ => rfl
  | .g, .g, .e => rfl
  | .g, .g, .g => rfl

/-- Right-inverse law: `x · x⁻¹ = e` (and `inv x = x` for `Z_2`). -/
theorem mul_inv : ∀ x : Z2, mul x (inv x) = .e
  | .e => rfl
  | .g => rfl

/-- Left-inverse law: `x⁻¹ · x = e`. -/
theorem inv_mul : ∀ x : Z2, mul (inv x) x = .e
  | .e => rfl
  | .g => rfl

end Z2

/-- `Z_2` as a `SymmetryGroup`.  Used by the Phase 1b Schelling-Ising
construction as the anonymity-bearing group acting on the spin space
by flipping. -/
def Z2Group : SymmetryGroup.{0} where
  carrier   := Z2
  one       := .e
  mul       := Z2.mul
  inv       := Z2.inv
  one_mul   := Z2.one_mul
  mul_one   := Z2.mul_one
  mul_assoc := Z2.mul_assoc
  mul_inv   := Z2.mul_inv
  inv_mul   := Z2.inv_mul

end UnifiedAggregation
