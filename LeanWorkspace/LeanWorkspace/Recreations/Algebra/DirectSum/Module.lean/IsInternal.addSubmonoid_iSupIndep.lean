import Mathlib

variable {R : Type u} [Ring R]

variable {ι : Type v} [dec_ι : DecidableEq ι]

variable {M : Type*} [AddCommGroup M] [Module R M]

theorem IsInternal.addSubmonoid_iSupIndep {M : Type*} [AddCommMonoid M] {A : ι → AddSubmonoid M}
    (h : IsInternal A) : iSupIndep A := iSupIndep_of_dfinsuppSumAddHom_injective _ h.injective

