import Mathlib

variable {α : Type*}

variable [Monoid α] {a b : α} {u : αˣ}

theorem dvd_mul_right : a ∣ b * u ↔ a ∣ b := Iff.intro (fun ⟨c, eq⟩ ↦ ⟨c * ↑u⁻¹, by rw [← mul_assoc, ← eq, Units.mul_inv_cancel_right]⟩)
    fun ⟨_, eq⟩ ↦ eq.symm ▸ (_root_.dvd_mul_right _ _).mul_right _

