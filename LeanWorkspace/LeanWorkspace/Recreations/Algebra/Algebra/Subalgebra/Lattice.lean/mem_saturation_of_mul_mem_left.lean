import Mathlib

variable {R S : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]
  {s : Subalgebra R S} {M : Submonoid S} {H : M ≤ s.toSubmonoid}

theorem mem_saturation_of_mul_mem_left {x y} (hxy : x * y ∈ s.saturation M H)
    (hx : x ∈ M) : y ∈ s.saturation M H := saturation_saturation.le ⟨_, hx, hxy⟩

