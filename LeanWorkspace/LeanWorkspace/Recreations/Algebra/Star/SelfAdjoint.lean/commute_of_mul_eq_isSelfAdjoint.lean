import Mathlib

variable {R A : Type*}

theorem commute_of_mul_eq_isSelfAdjoint {R : Type*} [Mul R] [StarMul R] (x y z : R)
    (hx : IsSelfAdjoint x) (hy : IsSelfAdjoint y) (hz : IsSelfAdjoint z) (hxyz : x * y = z) :
    Commute x y := by
  grind [IsSelfAdjoint.commute_iff hx hy]

