import Mathlib

variable (R : Type u) {A : Type v} {B : Type w}

variable [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

theorem mem_iSup_of_mem {ι : Sort*} {S : ι → Subalgebra R A} (i : ι) {x : A} (hx : x ∈ S i) :
    x ∈ iSup S := le_iSup S i hx

