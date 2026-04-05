import Mathlib

variable {σ : Type*} {τ : Type*} {υ : Type*} {R : Type*} [CommSemiring R]

theorem comap_id_apply (x : σ → R) : MvPolynomial.comap (AlgHom.id R (MvPolynomial σ R)) x = x := by
  funext i
  simp only [MvPolynomial.comap, AlgHom.id_apply, aeval_X]

