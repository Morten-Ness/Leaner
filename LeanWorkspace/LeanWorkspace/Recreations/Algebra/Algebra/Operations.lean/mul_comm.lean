import Mathlib

variable {ι : Sort uι}

variable {R : Type u} [CommSemiring R]

variable {A : Type v} [CommSemiring A] [Algebra R A]

variable {M N : Submodule R A} {m n : A}

theorem mul_comm : M * N = N * M := le_antisymm (Submodule.mul_le.2 fun _r hrm _s hsn => Submodule.mul_mem_mul_rev hsn hrm)
    (Submodule.mul_le.2 fun _r hrn _s hsm => Submodule.mul_mem_mul_rev hsm hrn)

