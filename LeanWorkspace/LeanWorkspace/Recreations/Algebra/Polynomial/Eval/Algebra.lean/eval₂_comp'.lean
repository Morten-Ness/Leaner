import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {a b : R} {m n : ℕ}

variable [CommSemiring R] [Semiring S] [Algebra R S] (x : S) (p q : R[X])

theorem eval₂_comp' : eval₂ (algebraMap R S) x (p.comp q) =
    eval₂ (algebraMap R S) (eval₂ (algebraMap R S) x q) p := by
  induction p using Polynomial.induction_on' with
  | add r s hr hs => simp only [add_comp, eval₂_add, hr, hs]
  | monomial n a => simp only [monomial_comp, Polynomial.eval₂_mul', eval₂_C, eval₂_monomial, Polynomial.eval₂_pow']

