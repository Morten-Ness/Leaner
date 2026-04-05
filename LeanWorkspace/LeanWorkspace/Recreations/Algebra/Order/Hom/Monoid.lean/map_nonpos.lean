import Mathlib

variable {F α β γ δ : Type*}

variable [FunLike F α β]

variable [Preorder α] [Zero α] [Preorder β] [Zero β] [OrderHomClass F α β]
  [ZeroHomClass F α β] (f : F) {a : α}

theorem map_nonpos (ha : a ≤ 0) : f a ≤ 0 := by
  rw [← map_zero f]
  exact OrderHomClass.mono _ ha

