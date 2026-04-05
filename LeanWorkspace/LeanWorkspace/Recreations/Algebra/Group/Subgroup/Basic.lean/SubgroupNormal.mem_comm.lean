import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {N : Type*} [Group N]

theorem SubgroupNormal.mem_comm {H K : Subgroup G} (hK : H ≤ K) [hN : (H.subgroupOf K).Normal]
    {a b : G} (hb : b ∈ K) (h : a * b ∈ H) : b * a ∈ H := by
  have := (Subgroup.normal_subgroupOf_iff hK).mp hN (a * b) b h hb
  rwa [mul_assoc, mul_assoc, mul_inv_cancel, mul_one] at this

