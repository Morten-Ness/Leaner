import Mathlib

variable (K : Type u) [CommSemiring K] (D D' : Type v) [Semiring D] [Algebra K D]
  [h : IsCentral K D] [Semiring D'] [Algebra K D']

theorem mem_center_iff {x : D} : x ∈ Subalgebra.center K D ↔ ∃ (a : K), x = algebraMap K D a := by
  rw [Algebra.IsCentral.center_eq_bot, Algebra.mem_bot]
  simp [eq_comm]

