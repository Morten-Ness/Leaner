import Mathlib

variable {α : Type*}

theorem sym_mul_self [Semiring α] [Invertible (2 : α)] (a : α) : SymAlg.sym (a * a) = SymAlg.sym a * SymAlg.sym a := by
  rw [SymAlg.sym_mul_sym, ← two_mul, invOf_mul_cancel_left]

