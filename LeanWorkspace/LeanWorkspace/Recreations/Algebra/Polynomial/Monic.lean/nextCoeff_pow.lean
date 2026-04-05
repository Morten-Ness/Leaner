import Mathlib

variable {R : Type u} {S : Type v} {a b : R} {m n : ℕ} {ι : Type y}

variable [Semiring R] {p q r : R[X]}

theorem nextCoeff_pow (hp : p.Monic) (n : ℕ) : (p ^ n).nextCoeff = n • p.nextCoeff := by
  induction n with
  | zero => rw [pow_zero, zero_smul, ← map_one (f := Polynomial.C), nextCoeff_C_eq_zero]
  | succ n ih => rw [pow_succ, Polynomial.Monic.nextCoeff_mul (hp.pow n) hp, ih, succ_nsmul]

