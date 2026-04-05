import Mathlib

variable {α : Type*}

variable [Semigroup α] {a b c : α}

theorem dvd_mul_of_dvd_left (h : a ∣ b) (c : α) : a ∣ b * c := h.trans (dvd_mul_right b c)

alias Dvd.dvd.mul_right := dvd_mul_of_dvd_left

