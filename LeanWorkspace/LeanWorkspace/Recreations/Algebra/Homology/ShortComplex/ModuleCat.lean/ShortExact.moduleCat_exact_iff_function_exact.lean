import Mathlib

variable {R : Type u} [Ring R]

variable (S : ShortComplex (ModuleCat.{v} R))

theorem ShortExact.moduleCat_exact_iff_function_exact :
    S.Exact ↔ Function.Exact S.f S.g := by
  rw [CategoryTheory.ShortComplex.moduleCat_exact_iff_range_eq_ker, LinearMap.exact_iff]
  tauto

