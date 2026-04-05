import Mathlib

variable (α β : Type*)

variable {α β} {a a₁ a₂ : α} {b b₁ b₂ : β}

variable [Semiring α] [PartialOrder α] [IsStrictOrderedRing α] [ExistsAddOfLE α]
  [AddCommMonoid β] [PartialOrder β] [IsOrderedCancelAddMonoid β] [Module α β]

variable [PosSMulStrictMono α β] {a₁ a₂ : α} {b₁ b₂ : β}

theorem smul_add_smul_lt_smul_add_smul (ha : a₁ < a₂) (hb : b₁ < b₂) :
    a₁ • b₂ + a₂ • b₁ < a₁ • b₁ + a₂ • b₂ := by
  obtain ⟨a, ha₀, rfl⟩ := lt_iff_exists_pos_add.1 ha
  rw [add_smul, add_smul, add_left_comm]
  gcongr
  assumption

