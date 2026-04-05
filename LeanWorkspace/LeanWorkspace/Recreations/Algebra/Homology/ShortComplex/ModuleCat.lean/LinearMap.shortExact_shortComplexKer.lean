import Mathlib

variable {R : Type u} [Ring R]

variable {M : Type v} [AddCommGroup M] [Module R M] {N : Type v} [AddCommGroup N] [Module R N]

theorem LinearMap.shortExact_shortComplexKer {f : M →ₗ[R] N} (h : Function.Surjective f) :
    f.shortComplexKer.ShortExact where
  exact := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr
    fun _ ↦ by simp [shortComplexKer]
  mono_f := (ModuleCat.mono_iff_injective _).mpr (LinearMap.ker f).injective_subtype
  epi_g := (ModuleCat.epi_iff_surjective _).mpr h

