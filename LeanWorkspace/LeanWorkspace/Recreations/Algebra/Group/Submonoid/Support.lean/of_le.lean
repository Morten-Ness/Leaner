import Mathlib

open scoped Pointwise

variable {G : Type*} [Group G] (M : Submonoid G)

theorem of_le {N : Submonoid G} (hM : M.IsMulSpanning) (h : M ≤ N) :
    N.IsMulSpanning := by aesop

