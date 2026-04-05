import Mathlib

variable {σ τ α R S : Type*} [CommSemiring R] [CommSemiring S]

theorem rename_rename (f : σ → τ) (g : τ → α) (p : MvPolynomial σ R) :
    MvPolynomial.rename g (MvPolynomial.rename f p) = MvPolynomial.rename (g ∘ f) p := by
  nth_rw 2 [MvPolynomial.rename]
  simp_rw [aeval_def, algebraMap_eq, MvPolynomial.rename, aeval_eq_eval₂Hom]
  rw [eval₂_comp_left (eval₂Hom (algebraMap R (MvPolynomial α R)) (X ∘ g)) C (X ∘ f) p]
  simp only [comp_def, eval₂Hom_X']
  refine eval₂Hom_congr ?_ rfl rfl
  ext1; simp only [comp_apply, RingHom.coe_comp, eval₂Hom_C]

