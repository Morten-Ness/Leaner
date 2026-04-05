import Mathlib

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] {p q : R[X]} {ι : Type*}

theorem degree_add_eq_of_leadingCoeff_add_ne_zero (h : leadingCoeff p + leadingCoeff q ≠ 0) :
    degree (p + q) = max p.degree q.degree := le_antisymm (degree_add_le _ _) <|
    match lt_trichotomy (degree p) (degree q) with
    | Or.inl hlt => by
      rw [Polynomial.degree_add_eq_right_of_degree_lt hlt, max_eq_right_of_lt hlt]
    | Or.inr (Or.inl HEq) =>
      le_of_not_gt fun hlt : max (degree p) (degree q) > degree (p + q) =>
        h <|
          show leadingCoeff p + leadingCoeff q = 0 by
            rw [HEq, max_self] at hlt
            rw [leadingCoeff, leadingCoeff, natDegree_eq_of_degree_eq HEq, ← coeff_add]
            exact Polynomial.coeff_natDegree_eq_zero_of_degree_lt hlt
    | Or.inr (Or.inr hlt) => by
      rw [Polynomial.degree_add_eq_left_of_degree_lt hlt, max_eq_left_of_lt hlt]

