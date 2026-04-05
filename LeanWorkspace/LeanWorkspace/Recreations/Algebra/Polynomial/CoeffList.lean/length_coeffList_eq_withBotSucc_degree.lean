import Mathlib

variable {R : Type*}

variable [Semiring R]

variable {P : R[X]}

theorem length_coeffList_eq_withBotSucc_degree (P : R[X]) : P.coeffList.length = P.degree.succ := by
  simp [Polynomial.coeffList]

