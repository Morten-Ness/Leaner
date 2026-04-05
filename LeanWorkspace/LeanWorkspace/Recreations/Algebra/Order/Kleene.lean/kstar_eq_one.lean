import Mathlib

variable {α β ι : Type*} {π : ι → Type*}

variable [KleeneAlgebra α] {a b c : α}

theorem kstar_eq_one : a∗ = 1 ↔ a ≤ 1 := ⟨le_kstar.trans_eq,
    fun h ↦ one_le_kstar.antisymm' <| kstar_le_of_mul_le_left le_rfl <| by rwa [one_mul]⟩

