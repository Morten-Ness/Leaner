import Mathlib

variable {M : Type*}

variable [CommMonoidWithZero M]

variable {p : M} (hp : Prime p)

theorem dvd_or_dvd {a b : M} (h : p ∣ a * b) : p ∣ a ∨ p ∣ b := hp.2.2 a b h

