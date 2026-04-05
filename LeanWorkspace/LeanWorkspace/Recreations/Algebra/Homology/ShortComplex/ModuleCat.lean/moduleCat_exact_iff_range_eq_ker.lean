import Mathlib

variable {R : Type u} [Ring R]

variable (S : ShortComplex (ModuleCat.{v} R))

theorem moduleCat_exact_iff_range_eq_ker :
    S.Exact ↔ LinearMap.range S.f.hom = LinearMap.ker S.g.hom := by
  rw [CategoryTheory.ShortComplex.moduleCat_exact_iff_ker_sub_range]
  aesop

