import Mathlib

variable {R : Type*}

variable [Semiring R]

variable {P : R[X]}

theorem length_coeffList_eq_ite [DecidableEq R] (P : R[X]) :
    P.coeffList.length = if P = 0 then 0 else P.natDegree + 1 := by
  by_cases h : P = 0 <;> simp [h, Polynomial.coeffList, withBotSucc_degree_eq_natDegree_add_one]

