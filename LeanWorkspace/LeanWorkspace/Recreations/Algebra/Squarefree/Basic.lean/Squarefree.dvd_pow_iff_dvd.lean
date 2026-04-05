import Mathlib

variable {R : Type*}

variable [CommMonoidWithZero R] [DecompositionMonoid R]

theorem Squarefree.dvd_pow_iff_dvd {x y : R} {n : ℕ} (hsq : Squarefree x) (h0 : n ≠ 0) :
    x ∣ y ^ n ↔ x ∣ y := ⟨hsq.isRadical n y, (·.pow h0)⟩

