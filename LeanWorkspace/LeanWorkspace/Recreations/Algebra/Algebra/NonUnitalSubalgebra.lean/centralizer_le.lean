import Mathlib

variable {R A : Type*} [CommSemiring R] [NonUnitalSemiring A] [Module R A] [IsScalarTower R A A]
  [SMulCommClass R A A]

theorem centralizer_le (s t : Set A) (h : s ⊆ t) : NonUnitalSubalgebra.centralizer R t ≤ NonUnitalSubalgebra.centralizer R s := Set.centralizer_subset h

