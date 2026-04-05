import Mathlib

variable {σ τ α R S : Type*} [CommSemiring R] [CommSemiring S]

variable (f : R →+* S) (k : σ → τ) (g : τ → S) (p : MvPolynomial σ R)

theorem eval_rename (g : τ → R) (p : MvPolynomial σ R) : eval g (MvPolynomial.rename k p) = eval (g ∘ k) p := MvPolynomial.eval₂_rename _ _ _ _

