import Mathlib

variable {σ τ α R S : Type*} [CommSemiring R] [CommSemiring S]

variable {f : σ → τ} (hf : Function.Injective f) {p q : MvPolynomial τ R}

theorem killCompl_comp_rename : (MvPolynomial.killCompl hf).comp (MvPolynomial.rename f) = AlgHom.id R _ := algHom_ext fun i => by
    dsimp
    rw [MvPolynomial.rename, MvPolynomial.killCompl, aeval_X, comp_apply, aeval_X, dif_pos ⟨i, rfl⟩,
      Equiv.ofInjective_symm_apply]

