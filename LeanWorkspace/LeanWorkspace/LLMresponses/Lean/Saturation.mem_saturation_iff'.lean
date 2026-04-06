import Mathlib

variable {M : Type*}

variable [CommMonoid M]

variable {s : Submonoid M} {x : M}

theorem mem_saturation_iff' : x ∈ s.saturation ↔ ∃ y, y * x ∈ s := by
  simpa [mul_comm] using (Submonoid.mem_saturation_iff (s := s) (x := x))
