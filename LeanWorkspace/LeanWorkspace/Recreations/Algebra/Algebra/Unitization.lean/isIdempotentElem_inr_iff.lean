import Mathlib

theorem isIdempotentElem_inr_iff (R : Type*) {A : Type*} [MulZeroClass R]
    [AddZeroClass A] [Mul A] [SMulWithZero R A] {a : A} :
    IsIdempotentElem (a : Unitization R A) ↔ IsIdempotentElem a := by
  simp only [IsIdempotentElem, ← Unitization.inr_mul, Unitization.inr_injective.eq_iff]

alias ⟨_, IsIdempotentElem.inr⟩ := isIdempotentElem_inr_iff

