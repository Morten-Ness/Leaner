import Mathlib

variable {R : Type u} {S : Type v} {a b : R} {m n : ℕ} {ι : Type y}

variable [Semiring R] {p q r : R[X]}

variable [Semiring S]

theorem MonicDegreeEq.degree [Nontrivial R] (p : MonicDegreeEq R n) :
    p.1.degree = n := degree_eq_of_le_of_coeff_ne_zero (degree_le_of_natDegree_le p.natDegree.le) (by simp [p.2.1])

