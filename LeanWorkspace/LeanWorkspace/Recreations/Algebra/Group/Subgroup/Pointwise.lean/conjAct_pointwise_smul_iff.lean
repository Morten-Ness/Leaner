import Mathlib

variable {α G A S : Type*}

variable [Group G] [AddGroup A] {s : Set G}

variable [Group α] [MulDistribMulAction α G]

theorem conjAct_pointwise_smul_iff {H : Subgroup G} {g : G} :
    ConjAct.toConjAct g • H = H ↔ g ∈ normalizer H := by
  rw [← (normalizer H : Subgroup G).inv_mem_iff]
  simp only [Subgroup.ext_iff, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
    ← ConjAct.toConjAct_inv, ConjAct.toConjAct_smul, mem_normalizer_iff, inv_inv, Iff.comm]

