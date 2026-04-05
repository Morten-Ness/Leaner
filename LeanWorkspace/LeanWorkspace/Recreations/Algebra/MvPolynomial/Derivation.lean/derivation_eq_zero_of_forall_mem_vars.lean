import Mathlib

variable {σ R A : Type*} [CommSemiring R] [AddCommMonoid A] [Module R A]
  [Module (MvPolynomial σ R) A]

theorem derivation_eq_zero_of_forall_mem_vars {D : Derivation R (MvPolynomial σ R) A}
    {f : MvPolynomial σ R} (h : ∀ i ∈ f.vars, D (X i) = 0) : D f = 0 := show D f = (0 : Derivation R (MvPolynomial σ R) A) f from MvPolynomial.derivation_eq_of_forall_mem_vars h

