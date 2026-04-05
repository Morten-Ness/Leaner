import Mathlib

variable {G R : Type*} [Group G] [Semiring R]

theorem smul_def (f : RingAut R) (r : R) : f • r = f r := rfl

