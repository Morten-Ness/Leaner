import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {a b : R} {m n : ℕ}

variable [Semiring R] {p q r : R[X]}

variable [Semiring S] {f : R →+* S} {p : R[X]}

theorem degree_map_eq_of_leadingCoeff_ne_zero (f : R →+* S) (hf : f (leadingCoeff p) ≠ 0) :
    degree (p.map f) = degree p := by
  refine Polynomial.degree_map_le.antisymm ?_
  have hp0 : p ≠ 0 :=
    leadingCoeff_ne_zero.mp fun hp0 => hf (_root_.trans (congr_arg _ hp0) f.map_zero)
  rw [degree_eq_natDegree hp0]
  refine le_degree_of_ne_zero ?_
  rw [coeff_map]
  exact hf

