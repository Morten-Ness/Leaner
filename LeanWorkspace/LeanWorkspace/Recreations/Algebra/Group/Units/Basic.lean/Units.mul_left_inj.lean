import Mathlib

variable {α : Type u}

variable [Monoid α]

variable (b c : αˣ) {u : αˣ}

theorem mul_left_inj (a : αˣ) {b c : α} : b * a = c * a ↔ b = c := ⟨fun h => by simpa only [Units.mul_inv_cancel_right] using congr_arg (fun x : α => x * ↑(a⁻¹ : αˣ)) h,
    congr_arg (· * a.val)⟩

