import Mathlib

variable {M : Type*}

variable [CommMonoid M]

variable {s : Submonoid M} {x : M}

theorem mem_saturation_iff' : x ∈ s.saturation ↔ ∃ y, y * x ∈ s := by
  simp_rw [Submonoid.mem_saturation_iff, mul_comm x]

