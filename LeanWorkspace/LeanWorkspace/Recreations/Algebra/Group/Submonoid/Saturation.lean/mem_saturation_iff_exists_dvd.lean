import Mathlib

variable {M : Type*}

variable [CommMonoid M]

variable {s : Submonoid M} {x : M}

theorem mem_saturation_iff_exists_dvd : x ∈ s.saturation ↔ ∃ m ∈ s, x ∣ m := by
  simp_rw [dvd_def, existsAndEq, and_true, Submonoid.mem_saturation_iff]

