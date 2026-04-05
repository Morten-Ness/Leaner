import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {a b : R} {m n : ℕ}

variable [Semiring R] {p q r : R[X]}

variable [Semiring S]

variable (f : R →+* S)

theorem map_comp (p q : R[X]) : Polynomial.map f (p.comp q) = (Polynomial.map f p).comp (Polynomial.map f q) := Polynomial.induction_on p (by simp only [Polynomial.map_C, forall_const, Polynomial.C_comp])
    (by
      simp +contextual only [Polynomial.map_add, Polynomial.add_comp, forall_const,
        imp_true_iff])
    (by
      simp +contextual only [pow_succ, ← mul_assoc, Polynomial.comp, forall_const,
        Polynomial.eval₂_mul_X, imp_true_iff, Polynomial.map_X, Polynomial.map_mul])

