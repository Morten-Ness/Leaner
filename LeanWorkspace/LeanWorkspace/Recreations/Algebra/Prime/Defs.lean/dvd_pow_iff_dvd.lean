import Mathlib

variable {M : Type*}

variable [CommMonoidWithZero M]

variable {p : M} (hp : Prime p)

theorem dvd_pow_iff_dvd {a : M} {n : ℕ} (hn : n ≠ 0) : p ∣ a ^ n ↔ p ∣ a := ⟨Prime.dvd_of_dvd_pow hp, (dvd_pow · hn)⟩

