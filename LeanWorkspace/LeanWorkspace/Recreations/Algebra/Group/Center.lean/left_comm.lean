import Mathlib

variable {M : Type*} {S T : Set M}

variable {a c : M} [Mul M]

theorem left_comm (h : IsMulCentral a) (b c) : a * (b * c) = b * (a * c) := by
  simp only [(h.comm _).eq, h.right_assoc]

-- cf. `Commute.right_comm`

