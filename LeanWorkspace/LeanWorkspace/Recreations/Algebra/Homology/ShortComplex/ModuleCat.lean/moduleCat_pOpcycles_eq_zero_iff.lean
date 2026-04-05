import Mathlib

variable {R : Type u} [Ring R]

variable (S : ShortComplex (ModuleCat.{v} R))

theorem moduleCat_pOpcycles_eq_zero_iff (x : S.X₂) :
    S.pOpcycles x = 0 ↔ x ∈ LinearMap.range S.f.hom := by
  simpa using CategoryTheory.ShortComplex.moduleCat_pOpcycles_eq_iff _ x 0

