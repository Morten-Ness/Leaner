import Mathlib

open scoped Pointwise

variable {G₀ G M A : Type*}

variable [Monoid M] [AddGroup A] [DistribMulAction M A] {a : M}

theorem smul_mem_pointwise_smul (m : A) (a : M) (S : AddSubgroup A) : m ∈ S → a • m ∈ a • S :=
by
  intro hm
  exact Set.mem_image_of_mem (a • ·) hm
