import Mathlib

variable {σ : Type*} {τ : Type*} {υ : Type*} {R : Type*} [CommSemiring R]

theorem comap_eq_id_of_eq_id (f : MvPolynomial σ R →ₐ[R] MvPolynomial σ R) (hf : ∀ φ, f φ = φ)
    (x : σ → R) : MvPolynomial.comap f x = x := by
  convert MvPolynomial.comap_id_apply x
  ext1 φ
  simp [hf, AlgHom.id_apply]

