import Mathlib

variable {M : Type*}

theorem Associated.prime [CommMonoidWithZero M] {p q : M} (h : p ~ᵤ q) (hp : Prime p) :
    Prime q := ⟨h.ne_zero_iff.1 hp.ne_zero,
    let ⟨u, hu⟩ := h
    ⟨fun ⟨v, hv⟩ => hp.not_unit ⟨v * u⁻¹, by simp [hv, Associated.symm hu]⟩, by
      rw [← hu]
      simp only [Units.isUnit, IsUnit.mul_right_dvd]
      intro a b
      exact hp.dvd_or_dvd⟩⟩

