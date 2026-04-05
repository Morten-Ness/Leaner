import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {a b : R} {m n : ℕ}

variable [Semiring R] {p q r : R[X]}

variable [Semiring S]

variable (f : R →+* S)

theorem map_monomial {n a} : (monomial n a).map f = monomial n (f a) := by
  dsimp only [Polynomial.map]
  rw [Polynomial.eval₂_monomial, ← C_mul_X_pow_eq_monomial]; rfl

