import Mathlib

variable {σ R A : Type*} [CommSemiring R] [AddCommMonoid A] [Module R A]
  [Module (MvPolynomial σ R) A]

theorem derivation_eq_of_forall_mem_vars {D₁ D₂ : Derivation R (MvPolynomial σ R) A}
    {f : MvPolynomial σ R} (h : ∀ i ∈ f.vars, D₁ (X i) = D₂ (X i)) : D₁ f = D₂ f := MvPolynomial.derivation_eqOn_supported h f.mem_supported_vars

