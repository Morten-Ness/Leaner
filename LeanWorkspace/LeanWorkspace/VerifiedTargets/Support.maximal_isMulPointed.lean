import Mathlib

open scoped Pointwise

variable {G : Type*} [Group G] (M : Submonoid G)

theorem maximal_isMulPointed (hMp : M.IsMulPointed) (hMs : M.IsMulSpanning) :
    Maximal Submonoid.IsMulPointed M := ⟨hMp, fun N hN h ↦ by rw [SetLike.le_def] at h ⊢; aesop⟩

