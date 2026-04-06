FAIL
import Mathlib

theorem isIdempotentElem_inr_iff (R : Type*) {A : Type*} [MulZeroClass R]
    [AddZeroClass A] [Mul A] [SMulWithZero R A] {a : A} :
    IsIdempotentElem (a : Unitization R A) ↔ IsIdempotentElem a := by
  change (((a : Unitization R A) * a = (a : Unitization R A)) ↔ a * a = a)
  simp [Unitization.inr_mul_inr]
