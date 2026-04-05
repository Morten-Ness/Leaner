import Mathlib

variable {M A B : Type*}

variable [MulOneClass M]

theorem mem_iSup_of_mem {ι : Sort*} {S : ι → Submonoid M} (i : ι) :
    ∀ {x : M}, x ∈ S i → x ∈ iSup S := by
  rw [← SetLike.le_def]
  exact le_iSup _ _

