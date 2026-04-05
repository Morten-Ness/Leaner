import Mathlib

variable {R n : Type*}

variable [NonUnitalNonAssocSemiring R] [Fintype n]

theorem matrix_injective [Nonempty n] : Function.Injective (RingCon.matrix (R := R) n) :=
  fun I J eq ↦ RingCon.ext fun r s ↦ by
    have := congr_fun (DFunLike.congr_fun eq (Matrix.of fun _ _ ↦ r)) (Matrix.of fun _ _ ↦ s)
    simpa using this

