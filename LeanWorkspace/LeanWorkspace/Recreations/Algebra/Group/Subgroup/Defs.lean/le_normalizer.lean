import Mathlib

open scoped Int

variable {G : Type*} [Group G] {A : Type*} [AddGroup A]

variable (H : Subgroup G)

theorem le_normalizer : H ≤ Subgroup.normalizer H := fun x xH n => by
  rw [SetLike.mem_coe, SetLike.mem_coe, H.mul_mem_cancel_right <| H.inv_mem xH,
    H.mul_mem_cancel_left xH]

