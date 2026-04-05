import Mathlib

open scoped Polynomial

variable (M : Type*) [Monoid M]

variable (R : Type*) [Semiring R]

variable [MulSemiringAction M R]

variable (S : Type*) [CommSemiring S] [MulSemiringAction M S]

theorem smul_eval_smul (m : M) (f : S[X]) (x : S) : (m • f).eval (m • x) = m • f.eval x := Polynomial.induction_on f (fun r ↦ by rw [smul_C, eval_C, eval_C])
    (fun f g ihf ihg ↦ by rw [smul_add, eval_add, ihf, ihg, eval_add, smul_add]) fun n r _ ↦ by
    rw [smul_mul', smul_pow', smul_C, Polynomial.smul_X, eval_mul, eval_C, eval_X_pow, eval_mul, eval_C,
      eval_X_pow, smul_mul', smul_pow']

