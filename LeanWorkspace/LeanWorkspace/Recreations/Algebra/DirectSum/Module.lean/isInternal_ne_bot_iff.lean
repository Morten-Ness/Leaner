import Mathlib

variable {R : Type u} [Ring R]

variable {ι : Type v} [dec_ι : DecidableEq ι]

variable {M : Type*} [AddCommGroup M] [Module R M]

theorem isInternal_ne_bot_iff {A : ι → Submodule R M} :
    IsInternal (fun i : {i // A i ≠ ⊥} ↦ A i) ↔ IsInternal A := by
  simp [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]

