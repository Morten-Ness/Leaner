FAIL
import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [DecidableEq β] [Group α] [MulAction α β] {s t : Finset β} {a : α} {b : β}

theorem mem_inv_smul_finset_iff : b ∈ a⁻¹ • s ↔ a • b ∈ s := by
  constructor
  · intro hb
    rcases Finset.mem_smul_finset.mp hb with ⟨y, hy, hya⟩
    rw [← hya, smul_smul, mul_left_inv, one_smul]
    exact hy
  · intro hb
    exact Finset.mem_smul_finset.mpr ⟨a • b, hb, by rw [smul_smul, mul_left_inv, one_smul]⟩
