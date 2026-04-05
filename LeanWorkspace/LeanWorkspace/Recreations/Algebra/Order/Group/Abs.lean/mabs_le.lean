import Mathlib

variable {G : Type*}

variable [CommGroup G] [LinearOrder G] [IsOrderedMonoid G] {a b c : G}

theorem mabs_le : |a|ₘ ≤ b ↔ b⁻¹ ≤ a ∧ a ≤ b := by rw [mabs_le', and_comm, inv_le']

