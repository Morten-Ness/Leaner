import Mathlib

variable {α β : Type*}

variable [Field α] [LinearOrder α] [IsStrictOrderedRing α]

theorem rat_inf_continuous_lemma {ε : α} {a₁ a₂ b₁ b₂ : α} :
    abs (a₁ - b₁) < ε → abs (a₂ - b₂) < ε → abs (a₁ ⊓ a₂ - b₁ ⊓ b₂) < ε := fun h₁ h₂ =>
  (abs_min_sub_min_le_max _ _ _ _).trans_lt (max_lt h₁ h₂)

