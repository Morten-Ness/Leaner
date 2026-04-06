import Mathlib

variable {M A B : Type*}

variable [MulOneClass M]

theorem mem_sSup_of_mem {S : Set (Submonoid M)} {s : Submonoid M} (hs : s ∈ S) :
    ∀ {x : M}, x ∈ s → x ∈ sSup S := by
  intro x hx
  exact Submonoid.mem_sSup_of_mem hs hx
