import Mathlib

variable {R M : Type*}

variable [Ring R] [AddCommGroup M] [Module R M]

variable {I : Ideal R} {r : R}

variable (M I) (s : Set R) (r : R)

theorem isTorsionBySet_quotient_set_smul :
    IsTorsionBySet R (M ⧸ s • (⊤ : Submodule R M)) s := (Module.isTorsionBySet_quotient_iff _ _).mpr fun _ _ h =>
    mem_set_smul_of_mem_mem h mem_top

