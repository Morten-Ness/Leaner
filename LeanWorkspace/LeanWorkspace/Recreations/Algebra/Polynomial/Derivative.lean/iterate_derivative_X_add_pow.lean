import Mathlib

open scoped Nat

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {A : Type z} {a b : R} {n : ℕ}

variable [CommSemiring R]

theorem iterate_derivative_X_add_pow (n k : ℕ) (c : R) :
    Polynomial.derivative^[k] ((Polynomial.X + Polynomial.C c) ^ n) = Nat.descFactorial n k • (Polynomial.X + Polynomial.C c) ^ (n - k) := by
  induction k with
  | zero => simp
  | succ k IH =>
      rw [Nat.sub_succ', Function.iterate_succ_apply', IH, Polynomial.derivative_smul,
        Polynomial.derivative_X_add_C_pow, map_natCast, Nat.descFactorial_succ, nsmul_eq_mul, nsmul_eq_mul,
        Nat.cast_mul]
      ring

