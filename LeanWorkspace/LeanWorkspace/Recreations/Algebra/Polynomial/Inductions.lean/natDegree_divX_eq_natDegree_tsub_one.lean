import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {A : Type z} {a b : R} {n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem natDegree_divX_eq_natDegree_tsub_one : p.divX.natDegree = p.natDegree - 1 := by
  apply map_natDegree_eq_sub (φ := Polynomial.divX_hom)
  · intro f
    simpa [Polynomial.divX_hom, Polynomial.divX_eq_zero_iff] using eq_C_of_natDegree_eq_zero
  · intro n c c0
    rw [← C_mul_X_pow_eq_monomial, divX_hom_toFun, Polynomial.divX_C_mul, Polynomial.divX_X_pow]
    split_ifs with n0
    · simp [n0]
    · exact natDegree_C_mul_X_pow (n - 1) c c0

