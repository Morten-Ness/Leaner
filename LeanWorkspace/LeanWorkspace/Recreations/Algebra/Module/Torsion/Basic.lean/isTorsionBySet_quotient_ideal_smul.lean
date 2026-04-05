import Mathlib

variable {R M : Type*}

variable [Ring R] [AddCommGroup M] [Module R M]

variable {I : Ideal R} {r : R}

variable (M I) (s : Set R) (r : R)

theorem isTorsionBySet_quotient_ideal_smul :
    IsTorsionBySet R (M ⧸ I • (⊤ : Submodule R M)) I := (Module.isTorsionBySet_quotient_iff _ _).mpr fun _ _ h => smul_mem_smul h ⟨⟩

