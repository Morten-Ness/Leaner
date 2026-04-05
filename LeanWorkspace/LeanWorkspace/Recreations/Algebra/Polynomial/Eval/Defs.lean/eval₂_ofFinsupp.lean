import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {a b : R} {m n : ℕ}

variable [Semiring R] {p q r : R[X]}

variable [Semiring S]

variable (f : R →+* S) (x : S)

variable [Semiring T]

theorem eval₂_ofFinsupp {f : R →+* S} {x : S} {p : R[ℕ]} :
    eval₂ f x (⟨p⟩ : R[X]) = liftNC (↑f) (powersHom S x) p := by
  simp only [Polynomial.eval₂_eq_sum, sum, support, coeff]
  rfl

