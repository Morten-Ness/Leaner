import Mathlib

variable {R S : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]
  {s : Subalgebra R S} {M : Submonoid S} {H : M ≤ s.toSubmonoid}

theorem le_saturation : s ≤ s.saturation M H := fun x hx ↦ ⟨1, one_mem M, by simpa⟩

