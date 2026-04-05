import Mathlib

variable {ι : Sort*} {M : Type*}

variable [Mul M]

theorem mem_iSup_of_mem {S : ι → Subsemigroup M} (i : ι) : ∀ {x : M}, x ∈ S i → x ∈ iSup S := by
  have : S i ≤ iSup S := le_iSup _ _
  tauto

