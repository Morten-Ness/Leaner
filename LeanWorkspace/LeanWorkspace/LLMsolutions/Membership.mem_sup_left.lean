import Mathlib

variable {M A B : Type*}

variable [MulOneClass M]

theorem mem_sup_left {S T : Submonoid M} : ∀ {x : M}, x ∈ S → x ∈ S ⊔ T := by
  intro x hx
  exact show x ∈ S ⊔ T from (le_sup_left : S ≤ S ⊔ T) hx
