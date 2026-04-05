import Mathlib

variable {R S : Type*}

theorem isDomain_iff_cancelMulZero_and_nontrivial [Semiring α] :
    IsDomain α ↔ IsCancelMulZero α ∧ Nontrivial α := ⟨fun _ ↦ ⟨inferInstance, inferInstance⟩, fun ⟨_, _⟩ ↦ {}⟩

