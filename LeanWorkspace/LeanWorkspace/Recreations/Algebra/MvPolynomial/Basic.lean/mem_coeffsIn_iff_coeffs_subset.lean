import Mathlib

open scoped Pointwise

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] [CommSemiring S₁] {p q : MvPolynomial σ R}

variable {R S σ : Type*} [CommSemiring R] [CommSemiring S]

variable [Module R S] {M N : Submodule R S} {p : MvPolynomial σ S} {s : σ} {i : σ →₀ ℕ} {x : S}
  {n : ℕ}

theorem mem_coeffsIn_iff_coeffs_subset : p ∈ MvPolynomial.coeffsIn σ M ↔ (p.coeffs : Set S) ⊆ M := by
  simp only [MvPolynomial.mem_coeffsIn, MvPolynomial.coeffs, Finset.coe_image, image_subset_iff]
  refine ⟨fun h x _ ↦ h x, fun h i ↦ ?_⟩
  by_cases hp : i ∈ p.support
  · exact h hp
  · convert M.zero_mem
    simpa using hp

