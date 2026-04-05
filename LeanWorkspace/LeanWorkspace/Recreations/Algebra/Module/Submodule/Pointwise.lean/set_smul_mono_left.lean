import Mathlib

variable {α : Type*} {R : Type*} {M : Type*}

variable [Semiring R] [AddCommMonoid M] [Module R M]

variable {S : Type*} [Monoid S]

variable [DistribMulAction S M]

variable (sR : Set R) (s : Set S) (N : Submodule R M)

theorem set_smul_mono_left {s t : Set S} (le : s ≤ t) :
    s • N ≤ t • N := Submodule.set_smul_le _ _ _ fun _ _ hr hm => Submodule.mem_set_smul_of_mem_mem (mem1 := le hr)
    (mem2 := hm)

