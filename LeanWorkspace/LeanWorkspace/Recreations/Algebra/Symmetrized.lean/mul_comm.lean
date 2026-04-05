import Mathlib

variable {α : Type*}

theorem mul_comm [Mul α] [AddCommSemigroup α] [One α] [OfNat α 2] [Invertible (2 : α)]
    (a b : αˢʸᵐ) :
    a * b = b * a := by rw [SymAlg.mul_def, SymAlg.mul_def, add_comm]

