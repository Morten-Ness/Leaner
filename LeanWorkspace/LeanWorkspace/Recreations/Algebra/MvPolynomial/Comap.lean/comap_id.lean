import Mathlib

variable {σ : Type*} {τ : Type*} {υ : Type*} {R : Type*} [CommSemiring R]

theorem comap_id : MvPolynomial.comap (AlgHom.id R (MvPolynomial σ R)) = id := by
  funext x
  exact MvPolynomial.comap_id_apply x

