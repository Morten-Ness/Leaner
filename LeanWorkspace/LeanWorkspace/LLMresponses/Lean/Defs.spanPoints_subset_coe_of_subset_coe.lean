FAIL
import Mathlib

variable (k : Type*) {V : Type*} (P : Type*) [Ring k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

variable {k P}

theorem spanPoints_subset_coe_of_subset_coe {s : Set P} {s₁ : AffineSubspace k P} (h : s ⊆ s₁) :
    spanPoints k s ⊆ s₁ := by
  classical
  rw [AffineSubspace.spanPoints_eq_iInf]
  intro p hp
  simp only [Set.mem_setOf_eq] at hp
  exact hp s₁ h
