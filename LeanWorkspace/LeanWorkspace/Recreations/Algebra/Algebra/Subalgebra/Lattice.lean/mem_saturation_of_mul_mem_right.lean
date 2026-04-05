import Mathlib

variable {R S : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]
  {s : Subalgebra R S} {M : Submonoid S} {H : M ≤ s.toSubmonoid}

theorem mem_saturation_of_mul_mem_right {x y} (hxy : x * y ∈ s.saturation M H)
    (hy : y ∈ M) : x ∈ s.saturation M H := Subalgebra.mem_saturation_of_mul_mem_left (mul_comm x y ▸ hxy) hy

