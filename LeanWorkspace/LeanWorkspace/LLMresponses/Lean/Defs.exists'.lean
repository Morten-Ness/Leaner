FAIL
import Mathlib

variable (R : Type*)

variable [NonAssocSemiring R]

variable [NoZeroDivisors R]

variable [Nontrivial R]

theorem exists' (R : Type*) [NonAssocRing R] [NoZeroDivisors R] [Nontrivial R] :
    CharZero R ∨ ∃ p : ℕ, Fact p.Prime ∧ CharP R p := by
  classical
  by_cases h0 : ringChar R = 0
  · left
    exact ringChar.eq_zero R
  · right
    refine ⟨ringChar R, ?_, ringChar.charP R⟩
    refine ⟨ringChar_prime_of_ne_zero h0⟩
