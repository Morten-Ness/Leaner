import Mathlib

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] {p q : R[X]} {ι : Type*}

theorem monic_of_natDegree_le_of_coeff_eq_one (n : ℕ) (pn : p.natDegree ≤ n) (p1 : p.coeff n = 1) :
    Polynomial.Monic p := by
  unfold Polynomial.Monic
  nontriviality
  refine (congr_arg _ <| Polynomial.natDegree_eq_of_le_of_coeff_ne_zero pn ?_).trans p1
  exact ne_of_eq_of_ne p1 one_ne_zero

