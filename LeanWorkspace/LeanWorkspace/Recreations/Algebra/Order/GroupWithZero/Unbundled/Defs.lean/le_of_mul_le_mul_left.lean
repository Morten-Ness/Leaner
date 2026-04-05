import Mathlib

variable (α : Type*)

variable [Mul α] [Zero α]

variable [Preorder α] {a b c d : α}

theorem le_of_mul_le_mul_left [PosMulReflectLE α] (bc : a * b ≤ a * c) (a0 : 0 < a) : b ≤ c := @ContravariantClass.elim α>0 α (fun x y => x * y) (· ≤ ·) _ ⟨a, a0⟩ _ _ bc

