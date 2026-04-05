import Mathlib

variable {α : Type*} {R : Type*} {M : Type*}

variable [Semiring R] [AddCommMonoid M] [Module R M]

variable {R G M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    [Group G] [DistribMulAction G M] [SMulCommClass G R M]
    {S : Submodule R M}

theorem stabilizer_coe :
    stabilizer G S = stabilizer G (S : Set M) := by
  ext
  rw [mem_stabilizer_iff, SetLike.ext'_iff, Submodule.coe_pointwise_smul,
    ← mem_stabilizer_iff]

