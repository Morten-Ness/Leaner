import Mathlib

open scoped Int

variable {G : Type*} [Group G] {A : Type*} [AddGroup A]

variable {S G : Type*} [Inv G] [SetLike S G] (s : S) [HasMemOrInvMem s]

theorem mem_of_inv_notMem (x : G) (h : x⁻¹ ∉ s) : x ∈ s := by
  rcases HasMemOrInvMem.mem_or_inv_mem (s := s) x with hx | hx
  · exact hx
  · exact False.elim (h hx)
