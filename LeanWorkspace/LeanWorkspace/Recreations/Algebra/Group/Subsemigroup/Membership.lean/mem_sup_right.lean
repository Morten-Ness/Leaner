import Mathlib

variable {ι : Sort*} {M : Type*}

variable [Mul M]

theorem mem_sup_right {S T : Subsemigroup M} : ∀ {x : M}, x ∈ T → x ∈ S ⊔ T := by
  have : T ≤ S ⊔ T := le_sup_right
  tauto

