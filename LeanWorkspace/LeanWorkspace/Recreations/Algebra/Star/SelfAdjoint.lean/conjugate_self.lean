import Mathlib

variable {R A : Type*}

variable [Semigroup R] [StarMul R]

theorem conjugate_self {x : R} (hx : IsSelfAdjoint x) {z : R} (hz : IsSelfAdjoint z) :
    IsSelfAdjoint (z * x * z) := by nth_rewrite 2 [← hz]; exact IsSelfAdjoint.conjugate hx z

