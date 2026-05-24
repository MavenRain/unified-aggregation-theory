/-
  UnifiedAggregation.Aggregation

  Aggregation as a left Kan extension along the orbit projection
  p : C ⥤ C // G.  The orbit groupoid and projection are declared
  here as Phase 0 stubs so the downstream regimes and trichotomy can
  be stated against the right signature; the concrete action-groupoid
  construction lands in Phase 1.
-/

import UnifiedAggregation.ChoiceRule
import CompCatTheory.Primitive.KanExtension

set_option autoImplicit false

universe u v

namespace UnifiedAggregation

open CompCatTheory

/-- The *orbit groupoid* `C // G`: morally the quotient category whose
objects are G-orbits of C-objects and whose morphisms include both
C-morphisms (within an orbit's representatives) and G-translations
(between representatives).

Phase 0 stub: declared as a `Type u` placeholder so the orbit projection
and aggregation can be typed.  Phase 1 replaces this with the genuine
action-groupoid construction. -/
def OrbitGroupoid {Obj : Type u} [Category.{u, u} Obj]
    {G : SymmetryGroup.{u}} (_act : GAction G Obj) : Type u :=
  Obj

/-- The orbit groupoid carries a category structure.  Phase 0 stub. -/
instance orbitGroupoidCategory {Obj : Type u} [Category.{u, u} Obj]
    {G : SymmetryGroup.{u}} (act : GAction G Obj) :
    Category.{u, u} (OrbitGroupoid act) := by
  sorry

/-- The orbit projection `p : C ⥤ C // G`.  Phase 0 stub. -/
def orbitProjection {Obj : Type u} [Category.{u, u} Obj]
    {G : SymmetryGroup.{u}} (act : GAction G Obj) :
    Obj ⥤ OrbitGroupoid act := by
  sorry

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
    {G : SymmetryGroup.{u}} (act : GAction G Obj)
    {D : Type v} [Category.{v, v} D]
    (F : ChoiceRule Obj D) :=
  LeftKanExtension (orbitProjection act) F

end UnifiedAggregation
