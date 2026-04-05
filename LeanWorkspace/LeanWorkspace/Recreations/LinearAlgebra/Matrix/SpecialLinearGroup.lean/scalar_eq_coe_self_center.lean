import Mathlib

variable {n : Type u} [DecidableEq n] [Fintype n] {R : Type v} [CommRing R]

variable {S : Type*} [CommRing S]

theorem scalar_eq_coe_self_center
    (A : center (Matrix.SpecialLinearGroup n R)) (i : n) :
    scalar n ((A : Matrix n n R) i i) = A := Matrix.SpecialLinearGroup.scalar_eq_self_of_mem_center A.property i

