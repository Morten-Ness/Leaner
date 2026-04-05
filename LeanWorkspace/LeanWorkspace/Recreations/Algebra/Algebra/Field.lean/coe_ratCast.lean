import Mathlib

variable (R A : Type*) [Field R] [DivisionRing A] [Algebra R A]

theorem coe_ratCast (q : ℚ) : ↑(q : R) = (q : A) := map_ratCast (algebraMap R A) q

