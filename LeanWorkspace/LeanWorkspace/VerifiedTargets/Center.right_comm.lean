import Mathlib

variable {M : Type*} {S T : Set M}

variable {a c : M} [Mul M]

theorem right_comm (h : IsMulCentral c) (a b) : a * b * c = a * c * b := by
  simp only [h.right_assoc, IsMulCentral.mid_assoc h, (h.comm _).eq]

