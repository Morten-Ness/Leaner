import Mathlib

variable {σ : Type*} {τ : Type*} {υ : Type*} {R : Type*} [CommSemiring R]

theorem comap_comp_apply (f : MvPolynomial σ R →ₐ[R] MvPolynomial τ R)
    (g : MvPolynomial τ R →ₐ[R] MvPolynomial υ R) (x : υ → R) :
    MvPolynomial.comap (g.comp f) x = MvPolynomial.comap f (MvPolynomial.comap g x) := by
  funext i
  trans aeval x (aeval (fun i => g (X i)) (f (X i)))
  · apply eval₂Hom_congr rfl rfl
    rw [AlgHom.comp_apply]
    suffices g = aeval fun i => g (X i) by rw [← this]
    exact aeval_unique g
  · simp only [MvPolynomial.comap, aeval_eq_eval₂Hom, map_eval₂Hom]
    refine eval₂Hom_congr ?_ rfl rfl
    ext r
    apply aeval_C

