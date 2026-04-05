import Mathlib

variable (α : Type*)

variable [Mul α] [Zero α]

variable [Preorder α] {a b c d : α}

theorem mul_le_mul_iff_left₀ [MulPosMono α] [MulPosReflectLE α] (a0 : 0 < a) :
    b * a ≤ c * a ↔ b ≤ c := @rel_iff_cov α>0 α (fun x y => y * x) (· ≤ ·) _ _ ⟨a, a0⟩ _ _

alias mul_le_mul_iff_of_pos_left := mul_le_mul_iff_right₀
alias mul_le_mul_iff_of_pos_right := mul_le_mul_iff_left₀
alias mul_lt_mul_iff_of_pos_left := mul_lt_mul_iff_right₀
alias mul_lt_mul_iff_of_pos_right := mul_lt_mul_iff_left₀

