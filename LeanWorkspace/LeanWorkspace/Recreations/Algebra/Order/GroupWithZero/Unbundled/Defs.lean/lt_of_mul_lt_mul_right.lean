import Mathlib

variable (α : Type*)

variable [Mul α] [Zero α]

variable [Preorder α] {a b c d : α}

theorem lt_of_mul_lt_mul_right [MulPosReflectLT α] (h : b * a < c * a) (a0 : 0 ≤ a) : b < c := @ContravariantClass.elim α≥0 α (fun x y => y * x) (· < ·) _ ⟨a, a0⟩ _ _ h

