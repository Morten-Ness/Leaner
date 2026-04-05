import Mathlib

variable {ι : Type*} {R : Type*} {M : Type*} {A : Type*}

theorem AddMonoidAlgebra.toDirectSum_pow [DecidableEq ι] [AddMonoid ι] [Semiring M]
    (f : AddMonoidAlgebra M ι) (n : ℕ) :
    (f ^ n).toDirectSum = f.toDirectSum ^ n := by
  classical exact map_pow addMonoidAlgebraRingEquivDirectSum f n

