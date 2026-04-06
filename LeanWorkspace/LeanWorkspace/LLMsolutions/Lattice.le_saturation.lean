import Mathlib

variable {R S : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]
  {s : Subalgebra R S} {M : Submonoid S} {H : M ≤ s.toSubmonoid}

theorem le_saturation : s ≤ s.saturation M H := by
  intro x hx
  exact ⟨1, M.one_mem, by simpa using hx⟩
