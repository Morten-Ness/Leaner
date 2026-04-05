import Mathlib

variable {R : Type u} {S : Type v}

variable {σ τ : Type*} {r : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] {p q : MvPolynomial σ R}

theorem le_degrees_add_right (h : Disjoint p.degrees q.degrees) : q.degrees ≤ (p + q).degrees := by
  simpa [add_comm] using MvPolynomial.le_degrees_add_left h.symm

