import Mathlib

variable {R : Type u} [Ring R]

variable {ι : Type v} [dec_ι : DecidableEq ι]

variable {M : Type*} [AddCommGroup M] [Module R M]

theorem isInternal_submodule_iff_iSupIndep_and_iSup_eq_top (A : ι → Submodule R M) :
    IsInternal A ↔ iSupIndep A ∧ iSup A = ⊤ := ⟨fun i ↦ ⟨i.submodule_iSupIndep, i.submodule_iSup_eq_top⟩,
    And.rec DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top⟩

