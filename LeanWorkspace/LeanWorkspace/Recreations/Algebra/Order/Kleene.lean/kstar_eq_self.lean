import Mathlib

variable {α β ι : Type*} {π : ι → Type*}

variable [KleeneAlgebra α] {a b c : α}

theorem kstar_eq_self : a∗ = a ↔ a * a = a ∧ 1 ≤ a := ⟨fun h ↦ ⟨by rw [← h, kstar_mul_kstar], one_le_kstar.trans_eq h⟩,
    fun h ↦ (kstar_le_of_mul_le_left h.2 h.1.le).antisymm le_kstar⟩

