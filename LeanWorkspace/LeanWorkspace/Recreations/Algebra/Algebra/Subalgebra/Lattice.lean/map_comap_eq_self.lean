import Mathlib

variable {R A B : Type*} [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

theorem map_comap_eq_self
    {f : A →ₐ[R] B} {S : Subalgebra R B} (h : S ≤ f.range) : (S.comap f).map f = S := by
  simpa only [inf_of_le_left h] using Subalgebra.map_comap_eq f S

