import Mathlib

variable {M : Type*} {N : Type*}

theorem setLike_mul_comm {S M : Type*} [SetLike S M] [Mul M] [MulMemClass S M]
    {s : S} [IsMulCommutative s] ⦃a b : M⦄ (ha : a ∈ s) (hb : b ∈ s) :
    a * b = b * a := isMulCommutative_iff_of_setLike.mp ‹_› a ha b hb

