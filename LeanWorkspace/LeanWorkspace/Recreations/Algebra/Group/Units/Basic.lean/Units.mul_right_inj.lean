import Mathlib

variable {α : Type u}

variable [Monoid α]

variable (b c : αˣ) {u : αˣ}

theorem mul_right_inj (a : αˣ) {b c : α} : (a : α) * b = a * c ↔ b = c := ⟨fun h => by simpa only [inv_mul_cancel_left] using congr_arg (fun x : α => ↑(a⁻¹ : αˣ) * x) h,
    congr_arg _⟩

