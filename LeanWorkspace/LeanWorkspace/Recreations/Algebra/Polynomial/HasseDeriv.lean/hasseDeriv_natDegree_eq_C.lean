import Mathlib

variable {R : Type*} [Semiring R] (k : ℕ) (f : R[X])

theorem hasseDeriv_natDegree_eq_C : f.hasseDeriv f.natDegree = Polynomial.C f.leadingCoeff := by
  have : _ ≤ 0 := Nat.sub_self f.natDegree ▸ Polynomial.natDegree_hasseDeriv_le ..
  rw [eq_C_of_natDegree_le_zero this, Polynomial.hasseDeriv_coeff, zero_add, Nat.choose_self,
    Nat.cast_one, one_mul, leadingCoeff]

