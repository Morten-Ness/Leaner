import Mathlib

variable (α : Type*)

variable [Mul α] [Zero α]

variable [Preorder α] {a b c d : α}

theorem le_of_mul_le_mul_right [MulPosReflectLE α] (bc : b * a ≤ c * a) (a0 : 0 < a) : b ≤ c := @ContravariantClass.elim α>0 α (fun x y => y * x) (· ≤ ·) _ ⟨a, a0⟩ _ _ bc

alias lt_of_mul_lt_mul_of_nonneg_left := lt_of_mul_lt_mul_left
alias lt_of_mul_lt_mul_of_nonneg_right := lt_of_mul_lt_mul_right
alias le_of_mul_le_mul_of_pos_left := le_of_mul_le_mul_left
alias le_of_mul_le_mul_of_pos_right := le_of_mul_le_mul_right

