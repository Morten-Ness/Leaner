import Mathlib

variable {R S : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]
  {s : Subalgebra R S} {M : Submonoid S} {H : M ≤ s.toSubmonoid}

theorem mem_saturation_of_mul_mem_right {x y} (hxy : x * y ∈ s.saturation M H)
    (hy : y ∈ M) : x ∈ s.saturation M H := by
  rcases hxy with ⟨z, hzM, hz_eq⟩
  refine ⟨y * z, M.mul_mem hy hzM, ?_⟩
  simpa [mul_assoc, mul_left_comm, mul_comm] using hz_eq
