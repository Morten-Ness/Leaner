import Mathlib

variable {R S σ : Type*}

theorem eval_polynomial_eval_finSuccEquiv {n : ℕ} {x : Fin n → R}
    [CommSemiring R] (f : MvPolynomial (Fin (n + 1)) R) (q : MvPolynomial (Fin n) R) :
    (eval x) (Polynomial.eval q (finSuccEquiv R n f)) = eval (Fin.cases (eval x q) x) f := by
  simp only [finSuccEquiv_apply, coe_eval₂Hom, MvPolynomial.polynomial_eval_eval₂, eval_eval₂]
  conv in RingHom.comp _ _ =>
    refine @RingHom.ext _ _ _ _ _ (RingHom.id _) fun r => ?_
    simp
  simp only [eval₂_id]
  congr
  funext i
  refine Fin.cases (by simp) (by simp) i

