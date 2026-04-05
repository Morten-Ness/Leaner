import Mathlib

variable (R : Type*) [Mul R] [Add R]

theorem coe_pow (f : R ≃+* R) (n : ℕ) : ⇑(f ^ n) = f^[n] := by
  induction n with
  | zero =>
    simp
  | succ n ih =>
    ext
    simp [pow_succ, ih]

