import Mathlib

variable {M : Type*}

theorem dvd_dvd_iff_associated [MonoidWithZero M] [IsLeftCancelMulZero M] {a b : M} :
    a ∣ b ∧ b ∣ a ↔ a ~ᵤ b := ⟨fun ⟨h1, h2⟩ => associated_of_dvd_dvd h1 h2, Associated.dvd_dvd⟩

