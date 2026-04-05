import Mathlib

variable {α β ι : Type*} {π : ι → Type*}

variable [KleeneAlgebra α] {a b c : α}

theorem kstar_idem (a : α) : a∗∗ = a∗ := kstar_eq_self.2 ⟨kstar_mul_kstar _, one_le_kstar⟩

