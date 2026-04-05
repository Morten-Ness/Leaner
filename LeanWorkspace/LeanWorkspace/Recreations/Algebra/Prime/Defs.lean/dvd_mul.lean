import Mathlib

variable {M : Type*}

variable [CommMonoidWithZero M]

variable {p : M} (hp : Prime p)

theorem dvd_mul {a b : M} : p ∣ a * b ↔ p ∣ a ∨ p ∣ b := ⟨Prime.dvd_or_dvd hp, (Or.elim · (dvd_mul_of_dvd_left · _) (dvd_mul_of_dvd_right · _))⟩

