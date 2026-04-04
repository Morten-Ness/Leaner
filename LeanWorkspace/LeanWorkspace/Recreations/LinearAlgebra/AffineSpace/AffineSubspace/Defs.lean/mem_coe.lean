import Mathlib

variable (k : Type*) {V : Type*} (P : Type*) [Ring k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

theorem mem_coe (p : P) (s : AffineSubspace k P) : p ∈ (s : Set P) ↔ p ∈ s := by simp

