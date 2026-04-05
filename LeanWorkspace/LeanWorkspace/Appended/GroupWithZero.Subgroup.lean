import Mathlib

section

open scoped Pointwise

variable {G₀ G M A : Type*}

variable [Monoid M] [AddGroup A] [DistribMulAction M A] {a : M}

theorem mem_smul_pointwise_iff_exists (m : A) (a : M) (S : AddSubgroup A) :
    m ∈ a • S ↔ ∃ s : A, s ∈ S ∧ a • s = m := (Set.mem_smul_set : m ∈ a • (S : Set A) ↔ _)

end

section

open scoped Pointwise

variable {G₀ G M A : Type*}

variable [Monoid M] [AddGroup A] [DistribMulAction M A] {a : M}

theorem smul_mem_pointwise_smul (m : A) (a : M) (S : AddSubgroup A) : m ∈ S → a • m ∈ a • S := (Set.smul_mem_smul_set : _ → _ ∈ a • (S : Set A))

end
