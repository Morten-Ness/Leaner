import Mathlib

open scoped Nat

variable {R S : Type*}

theorem eval_sumIDeriv_of_pos
    [CommRing R] [Nontrivial R] [NoZeroDivisors R] (p : R[X]) {q : ℕ} (hq : 0 < q) :
    ∃ gp : R[X], gp.natDegree ≤ p.natDegree - q ∧
      ∀ (r : R) {p' : R[X]},
        p = ((X : R[X]) - C r) ^ (q - 1) * p' →
        eval r (Polynomial.sumIDeriv p) = (q - 1)! • p'.eval r + q ! • eval r gp := by
  simpa using Polynomial.aeval_sumIDeriv_of_pos R p hq Function.injective_id

