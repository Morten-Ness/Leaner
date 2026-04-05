import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {a b : R} {n : ℕ}

variable [CommRing R] [IsDomain R] {p q : R[X]}

theorem roots_pow (p : R[X]) (n : ℕ) : (p ^ n).roots = n • p.roots := by
  induction n with
  | zero => rw [pow_zero, Polynomial.roots_one, zero_smul, empty_eq_zero]
  | succ n ihn =>
    rcases eq_or_ne p 0 with (rfl | hp)
    · rw [zero_pow n.succ_ne_zero, Polynomial.roots_zero, smul_zero]
    · rw [pow_succ, Polynomial.roots_mul (mul_ne_zero (pow_ne_zero _ hp) hp), ihn, add_smul, one_smul]

