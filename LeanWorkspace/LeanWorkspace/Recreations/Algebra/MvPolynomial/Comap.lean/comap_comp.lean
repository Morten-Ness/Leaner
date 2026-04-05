import Mathlib

variable {σ : Type*} {τ : Type*} {υ : Type*} {R : Type*} [CommSemiring R]

theorem comap_comp (f : MvPolynomial σ R →ₐ[R] MvPolynomial τ R)
    (g : MvPolynomial τ R →ₐ[R] MvPolynomial υ R) : MvPolynomial.comap (g.comp f) = MvPolynomial.comap f ∘ MvPolynomial.comap g := by
  funext x
  exact MvPolynomial.comap_comp_apply _ _ _

