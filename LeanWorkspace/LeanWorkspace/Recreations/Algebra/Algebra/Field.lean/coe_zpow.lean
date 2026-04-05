import Mathlib

variable {R : Type*} (A : Type*) [Semifield R] [DivisionSemiring A] [Algebra R A]

theorem coe_zpow (r : R) (z : ℤ) : ↑(r ^ z) = (r : A) ^ z := map_zpow₀ (algebraMap R A) r z

