import Mathlib

variable {R : Type u} [Ring R]

variable (S : ShortComplex (ModuleCat.{v} R))

theorem Exact.moduleCat_range_eq_ker (hS : S.Exact) :
    LinearMap.range S.f.hom = LinearMap.ker S.g.hom := by
  simpa only [CategoryTheory.ShortComplex.moduleCat_exact_iff_range_eq_ker] using hS

