import Mathlib

variable {α : Type*} {R : Type*} {M : Type*}

variable [Semiring R] [AddCommMonoid M] [Module R M]

variable {R G M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    [Group G] [DistribMulAction G M] [SMulCommClass G R M]
    {S : Submodule R M}

theorem mem_stabilizer_submodule_iff_map_eq {e : G} :
    e ∈ stabilizer G S ↔ S.map (DistribSMul.toLinearMap R M e) = S := by
  rfl

