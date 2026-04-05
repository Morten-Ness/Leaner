import Mathlib

variable {ι : Sort uι}

variable {R : Type u} [CommSemiring R]

variable {A : Type v} [CommSemiring A] [Algebra R A]

variable {M N : Submodule R A} {m n : A}

theorem mem_div_iff_forall_mul_mem {x : A} {I J : Submodule R A} : x ∈ I / J ↔ ∀ y ∈ J, x * y ∈ I := Iff.refl _

