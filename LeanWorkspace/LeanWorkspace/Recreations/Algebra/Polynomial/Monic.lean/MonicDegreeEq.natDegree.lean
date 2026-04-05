import Mathlib

variable {R : Type u} {S : Type v} {a b : R} {m n : ℕ} {ι : Type y}

variable [Semiring R] {p q r : R[X]}

variable [Semiring S]

theorem MonicDegreeEq.natDegree [Nontrivial R] (p : MonicDegreeEq R n) :
    p.1.natDegree = n := natDegree_eq_of_le_of_coeff_ne_zero (natDegree_le_iff_coeff_eq_zero.mpr p.2.2) (by simp [p.2.1])

