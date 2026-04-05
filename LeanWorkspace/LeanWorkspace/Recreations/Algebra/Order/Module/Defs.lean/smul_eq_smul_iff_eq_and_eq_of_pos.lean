import Mathlib

variable (α β : Type*)

variable {α β} {a a₁ a₂ : α} {b b₁ b₂ : β}

variable [Zero α] [Zero β] [SMulWithZero α β]

variable [PartialOrder α] [PartialOrder β]

theorem smul_eq_smul_iff_eq_and_eq_of_pos [PosSMulStrictMono α β] [SMulPosStrictMono α β]
    (ha : a₁ ≤ a₂) (hb : b₁ ≤ b₂) (h₁ : 0 < a₁) (h₂ : 0 < b₂) :
    a₁ • b₁ = a₂ • b₂ ↔ a₁ = a₂ ∧ b₁ = b₂ := by
  refine ⟨fun h ↦ ?_, by rintro ⟨rfl, rfl⟩; rfl⟩
  simp only [eq_iff_le_not_lt, ha, hb, true_and]
  refine ⟨fun ha ↦ h.not_lt ?_, fun hb ↦ h.not_lt ?_⟩
  · exact (smul_le_smul_of_nonneg_left hb h₁.le).trans_lt (smul_lt_smul_of_pos_right ha h₂)
  · exact (smul_lt_smul_of_pos_left hb h₁).trans_le (smul_le_smul_of_nonneg_right ha h₂.le)

