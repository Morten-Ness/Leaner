import Mathlib

variable (R : Type u) {A : Type v} {B : Type w}

variable [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

theorem coe_sInf (S : Set (Subalgebra R A)) : (↑(sInf S) : Set A) = ⋂ s ∈ S, ↑s := sInf_image

