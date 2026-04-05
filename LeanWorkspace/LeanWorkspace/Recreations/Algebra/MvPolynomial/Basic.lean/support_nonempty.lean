import Mathlib

open scoped Pointwise

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] [CommSemiring S₁] {p q : MvPolynomial σ R}

theorem support_nonempty {p : MvPolynomial σ R} : p.support.Nonempty ↔ p ≠ 0 := by
  rw [Finset.nonempty_iff_ne_empty, ne_eq, MvPolynomial.support_eq_empty]

