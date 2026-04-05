import Mathlib

variable {R : Type u} [Ring R]

variable {M : Type v} [AddCommGroup M] [Module R M] {N : Type v} [AddCommGroup N] [Module R N]

variable {L : Type v} [AddCommGroup L] [Module R L]

theorem ModuleCat.shortComplex_shortExact (S : ShortComplex (ModuleCat.{v} R))
    (exac : Function.Exact S.f S.g) (inj : Function.Injective S.f)
    (surj : Function.Surjective S.g) : S.ShortExact where
  exact := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr exac
  mono_f := (ModuleCat.mono_iff_injective _).mpr inj
  epi_g := (ModuleCat.epi_iff_surjective _).mpr surj

