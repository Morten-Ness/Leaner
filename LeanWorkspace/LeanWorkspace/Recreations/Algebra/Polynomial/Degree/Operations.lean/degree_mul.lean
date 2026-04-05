import Mathlib

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R]

variable [NoZeroDivisors R] {p q : R[X]}

theorem degree_mul : degree (p * q) = degree p + degree q := letI := Classical.decEq R
  if hp0 : p = 0 then by simp only [hp0, degree_zero, zero_mul, WithBot.bot_add]
  else
    if hq0 : q = 0 then by simp only [hq0, degree_zero, mul_zero, WithBot.add_bot]
    else Polynomial.degree_mul' <| mul_ne_zero (mt leadingCoeff_eq_zero.1 hp0) (mt leadingCoeff_eq_zero.1 hq0)

