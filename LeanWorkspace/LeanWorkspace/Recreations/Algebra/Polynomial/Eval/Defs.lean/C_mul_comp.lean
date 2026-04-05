import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {a b : R} {m n : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem C_mul_comp : (Polynomial.C a * p).comp r = Polynomial.C a * p.comp r := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq, mul_add]
  | monomial n b => simp [mul_assoc]

