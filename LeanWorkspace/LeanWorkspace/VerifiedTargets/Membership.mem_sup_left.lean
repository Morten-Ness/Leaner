import Mathlib

variable {M A B : Type*}

variable [MulOneClass M]

theorem mem_sup_left {S T : Submonoid M} : ∀ {x : M}, x ∈ S → x ∈ S ⊔ T := by
  rw [← SetLike.le_def]
  exact le_sup_left

