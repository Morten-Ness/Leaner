import Mathlib

variable {σ R A : Type*} [CommSemiring R] [AddCommMonoid A] [Module R A]
  [Module (MvPolynomial σ R) A]

theorem derivation_eqOn_supported {D₁ D₂ : Derivation R (MvPolynomial σ R) A} {s : Set σ}
    (h : Set.EqOn (D₁ ∘ X) (D₂ ∘ X) s) {f : MvPolynomial σ R} (hf : f ∈ supported R s) :
    D₁ f = D₂ f := Derivation.eqOn_adjoin (Set.forall_mem_image.2 h) hf

