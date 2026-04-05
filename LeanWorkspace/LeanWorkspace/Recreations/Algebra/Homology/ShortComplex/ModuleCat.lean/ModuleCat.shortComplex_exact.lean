import Mathlib

variable {R : Type u} [Ring R]

variable {M : Type v} [AddCommGroup M] [Module R M] {N : Type v} [AddCommGroup N] [Module R N]

variable {L : Type v} [AddCommGroup L] [Module R L]

theorem ModuleCat.shortComplex_exact (S : ShortComplex (ModuleCat.{v} R))
    (exac : Function.Exact S.f S.g) : S.Exact := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr exac

