import Mathlib

variable {R : Type u} {S : Type v} {ι : Type w} {a b : R} {m n : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem coeff_add_eq_left_of_lt (qn : q.natDegree < n) : (p + q).coeff n = p.coeff n := (coeff_add _ _ _).trans <|
    (congr_arg _ <| coeff_eq_zero_of_natDegree_lt <| qn).trans <| add_zero _

