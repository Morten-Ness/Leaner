import Mathlib

open scoped Pointwise

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] [CommSemiring S₁] {p q : MvPolynomial σ R}

variable (f : R →+* S₁)

theorem map_surjective (hf : Function.Surjective f) :
    Function.Surjective (MvPolynomial.map f : MvPolynomial σ R → MvPolynomial σ S₁) := fun p => by
  induction p using MvPolynomial.induction_on' with
  | monomial i fr =>
    obtain ⟨r, rfl⟩ := hf fr
    exact ⟨monomial i r, MvPolynomial.map_monomial _ _ _⟩
  | add a b ha hb =>
    obtain ⟨a, rfl⟩ := ha
    obtain ⟨b, rfl⟩ := hb
    exact ⟨a + b, map_add _ _ _⟩

