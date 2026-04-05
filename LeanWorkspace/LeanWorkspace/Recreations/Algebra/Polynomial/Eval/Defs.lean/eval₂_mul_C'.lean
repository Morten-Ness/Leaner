import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {a b : R} {m n : ℕ}

variable [Semiring R] {p q r : R[X]}

variable [Semiring S]

variable (f : R →+* S) (x : S)

variable [Semiring T]

theorem eval₂_mul_C' (h : Commute (f a) x) : eval₂ f x (p * Polynomial.C a) = eval₂ f x p * f a := by
  rw [Polynomial.eval₂_mul_noncomm, Polynomial.eval₂_C]
  intro k
  by_cases hk : k = 0
  · simp only [hk, h, coeff_C_zero]
  · simp only [coeff_C_ne_zero hk, map_zero, Commute.zero_left]

