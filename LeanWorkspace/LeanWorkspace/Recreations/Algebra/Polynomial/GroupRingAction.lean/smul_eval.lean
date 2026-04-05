import Mathlib

open scoped Polynomial

variable (M : Type*) [Monoid M]

variable (R : Type*) [Semiring R]

variable [MulSemiringAction M R]

variable (S : Type*) [CommSemiring S] [MulSemiringAction M S]

variable (G : Type*) [Group G]

theorem smul_eval [MulSemiringAction G S] (g : G) (f : S[X]) (x : S) :
    (g • f).eval x = g • f.eval (g⁻¹ • x) := by
  rw [← Polynomial.smul_eval_smul, smul_inv_smul]

