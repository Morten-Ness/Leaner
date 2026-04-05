import Mathlib

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {s : σ →₀ ℕ}

variable (R) [CommSemiring R]

variable (n : ℕ)

theorem finSuccEquiv_comp_C_eq_C {R : Type u} [CommSemiring R] (n : ℕ) :
    (↑(MvPolynomial.finSuccEquiv R n).symm : Polynomial (MvPolynomial (Fin n) R) →+* _).comp
        (Polynomial.C.comp MvPolynomial.C) =
      (MvPolynomial.C : R →+* MvPolynomial (Fin n.succ) R) := by
  refine RingHom.ext fun x => ?_
  rw [RingHom.comp_apply]
  refine
    (MvPolynomial.finSuccEquiv R n).injective
      (Trans.trans ((MvPolynomial.finSuccEquiv R n).apply_symm_apply _) ?_)
  simp only [MvPolynomial.finSuccEquiv_apply, MvPolynomial.eval₂Hom_C]

