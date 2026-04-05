import Mathlib

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem Monic.eq_X_add_C (hm : p.Monic) (hnd : p.natDegree = 1) : p = Polynomial.X + Polynomial.C (p.coeff 0) := by
  rw [← one_mul Polynomial.X, ← C_1, ← hm.coeff_natDegree, hnd, ← Polynomial.eq_X_add_C_of_natDegree_le_one hnd.le]

