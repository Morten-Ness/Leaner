import Mathlib

variable {M : Type*}

variable [CommMonoid M]

variable {s : Submonoid M} {x : M}

theorem mem_saturation_iff : x ∈ s.saturation ↔ ∃ y, x * y ∈ s := by
  simpa [Submonoid.mem_saturation_iff] using (Submonoid.mem_saturation_iff (S := s) (x := x))
