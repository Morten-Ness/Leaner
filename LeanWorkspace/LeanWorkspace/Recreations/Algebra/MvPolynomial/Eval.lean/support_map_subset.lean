import Mathlib

open scoped Pointwise

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] [CommSemiring S₁] {p q : MvPolynomial σ R}

variable (f : R →+* S₁)

theorem support_map_subset (p : MvPolynomial σ R) : (MvPolynomial.map f p).support ⊆ p.support := by
  simp only [Finset.subset_iff, mem_support_iff]
  intro x hx
  contrapose! hx
  rw [MvPolynomial.coeff_map, hx, map_zero]

