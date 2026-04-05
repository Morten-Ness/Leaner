import Mathlib

open scoped Pointwise

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] [CommSemiring S₁] {p q : MvPolynomial σ R}

variable (f : R →+* S₁)

theorem map_injective (hf : Function.Injective f) :
    Function.Injective (MvPolynomial.map f : MvPolynomial σ R → MvPolynomial σ S₁) := by
  intro p q h
  simp only [MvPolynomial.ext_iff, MvPolynomial.coeff_map] at h ⊢
  intro m
  exact hf (h m)

