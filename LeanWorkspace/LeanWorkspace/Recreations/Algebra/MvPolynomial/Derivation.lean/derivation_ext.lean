import Mathlib

variable {σ R A : Type*} [CommSemiring R] [AddCommMonoid A] [Module R A]
  [Module (MvPolynomial σ R) A]

theorem derivation_ext {D₁ D₂ : Derivation R (MvPolynomial σ R) A} (h : ∀ i, D₁ (X i) = D₂ (X i)) :
    D₁ = D₂ := Derivation.ext fun _ => MvPolynomial.derivation_eq_of_forall_mem_vars fun i _ => h i

