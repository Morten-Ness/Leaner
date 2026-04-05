import Mathlib

variable {M : Type*} {S T : Set M}

variable {a c : M} [Mul M]

theorem mid_assoc {z : M} (h : IsMulCentral z) (a c) : a * z * c = a * (z * c) := by
  rw [h.comm, ← h.right_assoc, ← h.comm, ← h.left_assoc, h.comm]

-- cf. `Commute.left_comm`

