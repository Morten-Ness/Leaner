import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {a b : R} {m n : ℕ}

variable [Semiring R] {p q r : R[X]}

variable [Semiring S]

variable (f : R →+* S)

theorem coeff_map_eq_comp (p : R[X]) (f : R →+* S) : (p.map f).coeff = f ∘ p.coeff := by
  ext n; exact Polynomial.coeff_map ..

