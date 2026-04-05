import Mathlib

variable (α β : Type*)

variable {α β} {a a₁ a₂ : α} {b b₁ b₂ : β}

variable [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
  [AddCommGroup β] [LinearOrder β] [IsOrderedAddMonoid β] [Module α β] [PosSMulStrictMono α β]
  {a : α} {b : β}

theorem smul_nonneg_iff : 0 ≤ a • b ↔ 0 ≤ a ∧ 0 ≤ b ∨ a ≤ 0 ∧ b ≤ 0 := ⟨nonneg_and_nonneg_or_nonpos_and_nonpos_of_smul_nonneg,
    fun h ↦ h.elim (and_imp.2 smul_nonneg) (and_imp.2 smul_nonneg_of_nonpos_of_nonpos)⟩

