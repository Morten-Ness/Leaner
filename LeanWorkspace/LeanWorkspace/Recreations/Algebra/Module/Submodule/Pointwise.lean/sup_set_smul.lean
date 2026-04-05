import Mathlib

variable {α : Type*} {R : Type*} {M : Type*}

variable [Semiring R] [AddCommMonoid M] [Module R M]

variable {S : Type*} [Monoid S]

variable [DistribMulAction S M]

variable (sR : Set R) (s : Set S) (N : Submodule R M)

theorem sup_set_smul (s t : Set S) :
    (s ⊔ t) • N = s • N ⊔ t • N := Submodule.set_smul_eq_of_le _ _ _
    (by rintro _ _ (hr | hr) hn
        · exact Submodule.mem_sup_left (Submodule.mem_set_smul_of_mem_mem hr hn)
        · exact Submodule.mem_sup_right (Submodule.mem_set_smul_of_mem_mem hr hn))
    (sup_le (Submodule.set_smul_mono_left _ le_sup_left) (Submodule.set_smul_mono_left _ le_sup_right))

