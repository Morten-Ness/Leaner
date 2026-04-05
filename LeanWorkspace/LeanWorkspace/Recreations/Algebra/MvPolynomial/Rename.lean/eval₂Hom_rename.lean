import Mathlib

variable {σ τ α R S : Type*} [CommSemiring R] [CommSemiring S]

variable (f : R →+* S) (k : σ → τ) (g : τ → S) (p : MvPolynomial σ R)

theorem eval₂Hom_rename : eval₂Hom f g (MvPolynomial.rename k p) = eval₂Hom f (g ∘ k) p := MvPolynomial.eval₂_rename _ _ _ _

