import Mathlib

variable {M : Type*}

variable [CommMonoidWithZero M]

variable {p : M} (hp : Prime p)

theorem not_dvd_mul {a b : M} (ha : ¬ p ∣ a) (hb : ¬ p ∣ b) : ¬ p ∣ a * b := Prime.dvd_mul hp.not.mpr <| not_or.mpr ⟨ha, hb⟩

