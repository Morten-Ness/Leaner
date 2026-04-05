import Mathlib

variable {α : Type*}

variable [Semigroup α] {a b c : α}

theorem IsLeftRegular.dvd_cancel_left (h : IsLeftRegular a) : a * b ∣ a * c ↔ b ∣ c := ⟨fun dvd ↦ have ⟨d, eq⟩ := dvd; ⟨d, h (eq.trans <| mul_assoc ..)⟩, mul_dvd_mul_left a⟩

