import Mathlib

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {s : σ →₀ ℕ}

variable (R) [CommSemiring R]

variable (n : ℕ)

theorem finSuccEquiv_eq :
    (MvPolynomial.finSuccEquiv R n : MvPolynomial (Fin (n + 1)) R →+* Polynomial (MvPolynomial (Fin n) R)) =
      eval₂Hom (Polynomial.C.comp (Polynomial.C : R →+* MvPolynomial (Fin n) R)) fun i : Fin (n + 1) =>
        Fin.cases Polynomial.X (fun k => Polynomial.C (Polynomial.X k)) i := by
  ext i : 2
  · simp only [MvPolynomial.finSuccEquiv, optionEquivLeft_apply, aeval_C, AlgEquiv.coe_trans, RingHom.coe_coe,
      coe_eval₂Hom, comp_apply, renameEquiv_apply, eval₂_C, RingHom.coe_comp, rename_C]
    rfl
  · refine Fin.cases ?_ ?_ i <;> simp [optionEquivLeft_apply, MvPolynomial.finSuccEquiv]

