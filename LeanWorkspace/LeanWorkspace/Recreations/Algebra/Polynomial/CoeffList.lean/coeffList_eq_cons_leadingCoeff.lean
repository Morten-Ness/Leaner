import Mathlib

variable {R : Type*}

variable [Semiring R]

variable {P : R[X]}

theorem coeffList_eq_cons_leadingCoeff (h : P ≠ 0) :
    ∃ ls, P.coeffList = P.leadingCoeff :: ls := by
  simp [Polynomial.coeffList, List.range_succ, withBotSucc_degree_eq_natDegree_add_one h]

