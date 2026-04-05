import Mathlib

variable {G M R K : Type*}

variable [Semifield K] [LinearOrder K] [IsStrictOrderedRing K] [Archimedean K] {x y ε : K}

variable [ExistsAddOfLE K]

theorem exists_mem_Ioc_zpow (hx : 0 < x) (hy : 1 < y) : ∃ n : ℤ, x ∈ Ioc (y ^ n) (y ^ (n + 1)) := let ⟨m, hle, hlt⟩ := exists_mem_Ico_zpow (inv_pos.2 hx) hy
  have hyp : 0 < y := lt_trans zero_lt_one hy
  ⟨-(m + 1), by rwa [zpow_neg, inv_lt_comm₀ (zpow_pos hyp _) hx], by
    rwa [neg_add, neg_add_cancel_right, zpow_neg, le_inv_comm₀ hx (zpow_pos hyp _)]⟩

