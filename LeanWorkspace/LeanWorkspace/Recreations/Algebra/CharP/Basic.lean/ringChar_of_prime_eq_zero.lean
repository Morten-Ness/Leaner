import Mathlib

variable (R : Type*)

variable {R} [NonAssocSemiring R]

theorem ringChar_of_prime_eq_zero [Nontrivial R] {p : ℕ} (hprime : Nat.Prime p)
    (hp0 : (p : R) = 0) : ringChar R = p := Or.resolve_left ((Nat.dvd_prime hprime).1 (ringChar.dvd hp0)) ringChar_ne_one

