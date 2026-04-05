import Mathlib

open scoped Int

variable {G : Type*} [Group G] {A : Type*} [AddGroup A]

variable {S G : Type*} [Inv G] [SetLike S G] (s : S) [HasMemOrInvMem s]

theorem inv_mem_of_notMem (x : G) (h : x ∉ s) : x⁻¹ ∈ s := by
  have := mem_or_inv_mem s x
  simp_all

