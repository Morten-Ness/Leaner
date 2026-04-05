import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem ext_iff {p q : R[X]} : p = q ↔ ∀ n, Polynomial.coeff p n = Polynomial.coeff q n := by
  rcases p with ⟨f : ℕ →₀ R⟩
  rcases q with ⟨g : ℕ →₀ R⟩
  simpa [Polynomial.coeff] using DFunLike.ext_iff (f := f) (g := g)

