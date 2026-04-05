import Mathlib

variable {R : Type u} [Ring R]

variable (S : ShortComplex (ModuleCat.{v} R))

theorem moduleCat_exact_iff_ker_sub_range :
    S.Exact ↔ LinearMap.ker S.g.hom ≤ LinearMap.range S.f.hom := by
  rw [CategoryTheory.ShortComplex.moduleCat_exact_iff]
  aesop

