import Mathlib

variable {α β : Type*}

variable [NonUnitalRing α] {a b c : α}

theorem dvd_add_left (h : a ∣ c) : a ∣ b + c ↔ a ∣ b := ⟨fun H => by simpa only [add_sub_cancel_right] using dvd_sub H h, fun h₂ => dvd_add h₂ h⟩

