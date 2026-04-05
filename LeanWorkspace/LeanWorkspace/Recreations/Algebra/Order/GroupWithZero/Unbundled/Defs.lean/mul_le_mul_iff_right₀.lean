import Mathlib

variable (α : Type*)

variable [Mul α] [Zero α]

variable [Preorder α] {a b c d : α}

theorem mul_le_mul_iff_right₀ [PosMulMono α] [PosMulReflectLE α] (a0 : 0 < a) :
    a * b ≤ a * c ↔ b ≤ c := @rel_iff_cov α>0 α (fun x y => x * y) (· ≤ ·) _ _ ⟨a, a0⟩ _ _

