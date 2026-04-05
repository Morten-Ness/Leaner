import Mathlib

variable {ι : Sort*} {M : Type*}

variable [Mul M]

theorem mem_sup_left {S T : Subsemigroup M} : ∀ {x : M}, x ∈ S → x ∈ S ⊔ T := by
  have : S ≤ S ⊔ T := le_sup_left
  tauto

