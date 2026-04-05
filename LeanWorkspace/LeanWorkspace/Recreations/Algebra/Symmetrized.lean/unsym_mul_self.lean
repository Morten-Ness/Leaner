import Mathlib

variable {α : Type*}

theorem unsym_mul_self [Semiring α] [Invertible (2 : α)] (a : αˢʸᵐ) :
    SymAlg.unsym (a * a) = SymAlg.unsym a * SymAlg.unsym a := by
  rw [SymAlg.mul_def, SymAlg.unsym_sym, ← two_mul, invOf_mul_cancel_left]

