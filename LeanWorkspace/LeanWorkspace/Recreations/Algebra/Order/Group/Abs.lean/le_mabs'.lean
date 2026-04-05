import Mathlib

variable {G : Type*}

variable [CommGroup G] [LinearOrder G] [IsOrderedMonoid G] {a b c : G}

theorem le_mabs' : a ≤ |b|ₘ ↔ b ≤ a⁻¹ ∨ a ≤ b := by rw [le_mabs, or_comm, le_inv']

