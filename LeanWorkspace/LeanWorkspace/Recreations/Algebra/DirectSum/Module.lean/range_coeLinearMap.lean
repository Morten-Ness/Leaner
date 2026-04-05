import Mathlib

variable {R : Type u} [Semiring R]

variable {ι : Type v} [dec_ι : DecidableEq ι]

variable {M : Type*} [AddCommMonoid M] [Module R M]

variable (A : ι → Submodule R M)

theorem range_coeLinearMap : LinearMap.range (DirectSum.coeLinearMap A) = ⨆ i, A i := (Submodule.iSup_eq_range_dfinsupp_lsum _).symm

