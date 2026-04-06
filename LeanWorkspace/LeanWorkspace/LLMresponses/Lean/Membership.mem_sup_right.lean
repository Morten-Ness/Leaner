import Mathlib

variable {M A B : Type*}

variable [MulOneClass M]

theorem mem_sup_right {S T : Submonoid M} : ∀ {x : M}, x ∈ T → x ∈ S ⊔ T := by
  intro x hx
  exact show x ∈ S ⊔ T from (le_sup_right : T ≤ S ⊔ T) hx
