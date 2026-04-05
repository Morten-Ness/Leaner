import Mathlib

variable {R A M : Type*}

variable [CommSemiring R]

variable [Semiring A] [Algebra R A]

theorem mem_algebraMapSubmonoid_of_mem {S : Type*} [Semiring S] [Algebra R S] {M : Submonoid R}
    (x : M) : algebraMap R S x ∈ Algebra.algebraMapSubmonoid S M := Set.mem_image_of_mem (algebraMap R S) x.2

