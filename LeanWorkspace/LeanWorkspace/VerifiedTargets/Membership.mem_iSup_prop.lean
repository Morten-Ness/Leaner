import Mathlib

variable {M A B : Type*}

variable [MulOneClass M]

theorem mem_iSup_prop {p : Prop} {S : p → Submonoid M} {x : M} :
    x ∈ ⨆ (h : p), S h ↔ x = 1 ∨ ∃ (h : p), x ∈ S h := by
  by_cases h : p <;>
  simp +contextual [h]

