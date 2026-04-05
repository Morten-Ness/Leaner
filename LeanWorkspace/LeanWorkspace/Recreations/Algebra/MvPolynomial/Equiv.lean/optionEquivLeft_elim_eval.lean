import Mathlib

open scoped Polynomial

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {s : σ →₀ ℕ}

variable (R) [CommSemiring R]

theorem optionEquivLeft_elim_eval (s : S₁ → R) (y : R) (f : MvPolynomial (Option S₁) R) :
    eval (fun x ↦ Option.elim x y s) f =
      Polynomial.eval y (Polynomial.map (eval s) (MvPolynomial.optionEquivLeft R S₁ f)) := by
  -- turn this into a def `Polynomial.mapAlgHom`
  let φ : (MvPolynomial S₁ R)[X] →ₐ[R] R[X] :=
    { Polynomial.mapRingHom (eval s) with
      commutes' := fun r => by
        convert Polynomial.map_C (eval s)
        exact (eval_C _).symm }
  change
    Polynomial.aeval (fun x ↦ Option.elim x y s) f =
      (Polynomial.aeval y).comp (φ.comp (MvPolynomial.optionEquivLeft _ _).toAlgHom) f
  congr 2
  apply MvPolynomial.algHom_ext
  rw [Option.forall]
  simp only [aeval_X, Option.elim_none, AlgEquiv.toAlgHom_eq_coe, AlgHom.coe_comp, comp_apply,
    Polynomial.coe_aeval_eq_eval, AlgHom.coe_mk, Polynomial.coe_mapRingHom, AlgHom.coe_coe,
    optionEquivLeft_apply, Polynomial.map_X, Polynomial.eval_X, Option.elim_some, Polynomial.map_C,
    eval_X, Polynomial.eval_C, implies_true, and_self, φ]

