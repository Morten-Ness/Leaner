import Mathlib

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {s : σ →₀ ℕ}

variable (R) [CommSemiring R]

variable [IsEmpty σ]

theorem aeval_injective_iff_of_isEmpty [CommSemiring S₁] [Algebra R S₁] {f : σ → S₁} :
    Function.Injective (Polynomial.aeval f : MvPolynomial σ R →ₐ[R] S₁) ↔
      Function.Injective (algebraMap R S₁) := by
  have : Polynomial.aeval f = (Algebra.ofId R S₁).comp (@MvPolynomial.isEmptyAlgEquiv R σ _ _).toAlgHom := by
    ext i
    exact IsEmpty.elim' ‹IsEmpty σ› i
  rw [this, ← Function.Injective.of_comp_iff' _ (@MvPolynomial.isEmptyAlgEquiv R σ _ _).bijective]
  rfl

