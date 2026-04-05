import Mathlib

variable (K : Type u) [CommSemiring K] (D D' : Type v) [Semiring D] [Algebra K D]
  [h : IsCentral K D] [Semiring D'] [Algebra K D']

theorem center_eq_bot : Subalgebra.center K D = ⊥ := eq_bot_iff.2 Algebra.IsCentral.out

