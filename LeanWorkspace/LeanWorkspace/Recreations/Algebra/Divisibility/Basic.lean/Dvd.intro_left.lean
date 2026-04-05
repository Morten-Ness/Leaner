import Mathlib

variable {α : Type*}

variable [CommSemigroup α] {a b c : α}

theorem Dvd.intro_left (c : α) (h : c * a = b) : a ∣ b := Dvd.intro c (by rw [mul_comm] at h; apply h)

alias dvd_of_mul_left_eq := Dvd.intro_left

