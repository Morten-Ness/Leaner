import Mathlib

variable {R : Type u} [Semiring R]

variable {ι : Type v} [dec_ι : DecidableEq ι]

variable {M : Type*} [AddCommMonoid M] [Module R M]

variable (A : ι → Submodule R M)

theorem IsInternal.submodule_iSupIndep (h : IsInternal A) : iSupIndep A := iSupIndep_of_dfinsupp_lsum_injective _ h.injective

