import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [DecidableEq β] [Group α] [MulAction α β] {s t : Finset β} {a : α} {b : β}

theorem inv_smul_mem_iff : a⁻¹ • b ∈ s ↔ b ∈ a • s := by
  constructor
  · intro hb
    rw [Finset.mem_smul_finset]
    exact ⟨a⁻¹ • b, hb, smul_inv_smul a b⟩
  · intro hb
    rw [Finset.mem_smul_finset] at hb
    rcases hb with ⟨x, hx, rfl⟩
    simpa using hx
