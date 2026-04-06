FAIL
import Mathlib

open Classical

variable {X : Type*}

theorem support_add (a b : FreeAbelianGroup X) : FreeAbelianGroup.support (a + b) ⊆ a.support + b.support := by
  intro x hx
  rw [FreeAbelianGroup.mem_support_iff] at hx ⊢
  contrapose! hx
  rw [FreeAbelianGroup.mem_support_iff] at hx
  rw [FreeAbelianGroup.mem_support_iff]
  simp only [not_not] at hx
  rw [FreeAbelianGroup.coeff_add]
  omega
