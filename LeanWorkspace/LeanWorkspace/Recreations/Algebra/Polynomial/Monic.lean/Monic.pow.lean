import Mathlib

variable {R : Type u} {S : Type v} {a b : R} {m n : ℕ} {ι : Type y}

variable [Semiring R] {p q r : R[X]}

theorem Monic.pow (hp : Polynomial.Monic p) : ∀ n : ℕ, Polynomial.Monic (p ^ n)
  | 0 => Polynomial.monic_one
  | n + 1 => by
    rw [pow_succ]
    exact (Polynomial.Monic.pow hp n).mul hp
