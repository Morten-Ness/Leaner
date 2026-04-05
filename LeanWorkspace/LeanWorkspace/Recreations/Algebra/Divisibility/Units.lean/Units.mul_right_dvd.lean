import Mathlib

variable {α : Type*}

variable [Monoid α] {a b : α} {u : αˣ}

theorem mul_right_dvd : a * u ∣ b ↔ a ∣ b := Iff.intro (fun ⟨c, eq⟩ => ⟨↑u * c, eq.trans (mul_assoc _ _ _)⟩) fun h =>
    dvd_trans (Dvd.intro (↑u⁻¹) (by rw [mul_assoc, u.mul_inv, mul_one])) h

