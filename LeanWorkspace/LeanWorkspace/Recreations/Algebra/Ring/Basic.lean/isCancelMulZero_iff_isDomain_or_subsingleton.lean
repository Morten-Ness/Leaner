import Mathlib

variable {R S : Type*}

theorem isCancelMulZero_iff_isDomain_or_subsingleton [Semiring α] :
    IsCancelMulZero α ↔ IsDomain α ∨ Subsingleton α := by
  refine ⟨fun t ↦ ?_, fun h ↦ h.elim (fun _ ↦ inferInstance) (fun _ ↦ inferInstance)⟩
  rw [or_iff_not_imp_right, not_subsingleton_iff_nontrivial]
  exact fun _ ↦ {}

