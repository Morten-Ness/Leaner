import Mathlib

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] {p q : R[X]} {ι : Type*}

theorem Monic.degree_mul (hq : Polynomial.Monic q) : degree (p * q) = degree p + degree q := letI := Classical.decEq R
  if hp : p = 0 then by simp [hp]
  else Polynomial.degree_mul' <| by rwa [hq.leadingCoeff, mul_one, Ne, leadingCoeff_eq_zero]

