import Mathlib

variable {R M : Type*}

variable [CommSemiring R] [AddCommMonoid M] [Module R M] (s : Set R) (a : R)

theorem isTorsionBy_iff_mem_ker_lsmul :
    IsTorsionBy R M a ↔ a ∈ LinearMap.ker (LinearMap.lsmul R M) := Iff.symm LinearMap.ext_iff

