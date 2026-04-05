import Mathlib

variable {R : Type u} {S : Type v}

variable {σ τ : Type*} {r : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] {p q : MvPolynomial σ R}

theorem totalDegree_monomial_le (s : σ →₀ ℕ) (c : R) :
    (monomial s c).totalDegree ≤ s.sum fun _ ↦ id := by
  if hc : c = 0 then
    simp only [hc, map_zero, MvPolynomial.totalDegree_zero, zero_le]
  else
    rw [MvPolynomial.totalDegree_monomial _ hc, Function.id_def]

