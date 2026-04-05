import Mathlib

variable {R : Type u} {S : Type v} {a b : R} {m n : ℕ} {ι : Type y}

variable [Semiring R] {p q r : R[X]}

theorem Monic.of_mul_monic_left (hp : p.Monic) (hpq : (p * q).Monic) : q.Monic := by
  contrapose! hpq
  rw [Polynomial.Monic.def] at hpq ⊢
  rwa [leadingCoeff_monic_mul hp]

