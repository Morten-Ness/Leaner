import Mathlib

open scoped Pointwise

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] [CommSemiring S₁] {p q : MvPolynomial σ R}

theorem coeffs_one_of_nontrivial [Nontrivial R] : MvPolynomial.coeffs (1 : MvPolynomial σ R) = {1} := by
  apply Finset.Subset.antisymm MvPolynomial.coeffs_one
  simp only [MvPolynomial.coeffs, Finset.singleton_subset_iff, Finset.mem_image]
  exact ⟨0, by simp⟩

