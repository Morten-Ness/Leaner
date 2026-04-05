import Mathlib

variable {α G A S : Type*}

variable [Group G] [AddGroup A] {s : Set G}

variable [Group α] [MulDistribMulAction α G]

theorem Normal.of_conjugate_fixed {H : Subgroup G} (h : ∀ g : G, (MulAut.conj g) • H = H) :
    H.Normal := by
  constructor
  intro n hn g
  rw [← h g, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv, MulAut.smul_def,
    MulAut.conj_apply, inv_inv, mul_assoc, mul_assoc, inv_mul_cancel, mul_one,
    ← mul_assoc, inv_mul_cancel, one_mul]
  exact hn

