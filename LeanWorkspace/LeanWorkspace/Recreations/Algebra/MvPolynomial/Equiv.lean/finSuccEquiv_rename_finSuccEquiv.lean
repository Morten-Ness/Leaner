import Mathlib

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {s : σ →₀ ℕ}

variable (R) [CommSemiring R]

variable (n : ℕ)

theorem finSuccEquiv_rename_finSuccEquiv (e : σ ≃ Fin n) (φ : MvPolynomial (Option σ) R) :
    ((MvPolynomial.finSuccEquiv R n) ((rename ((Equiv.optionCongr e).trans (_root_.finSuccEquiv n).symm)) φ)) =
      Polynomial.map (rename e).toRingHom (MvPolynomial.optionEquivLeft R σ φ) := by
  suffices (MvPolynomial.finSuccEquiv R n).toRingEquiv.toRingHom.comp (rename ((Equiv.optionCongr e).trans
        (_root_.finSuccEquiv n).symm)).toRingHom =
      (Polynomial.mapRingHom (rename e).toRingHom).comp (MvPolynomial.optionEquivLeft R σ) by
    exact DFunLike.congr_fun this φ
  apply ringHom_ext
  · simp [Polynomial.algebraMap_apply, algebraMap_eq, MvPolynomial.finSuccEquiv_apply, optionEquivLeft_apply]
  · rintro (i | i) <;> simp [MvPolynomial.finSuccEquiv_apply, optionEquivLeft_apply]

