import Mathlib

variable {R A : Type*} [CommSemiring R] [NonUnitalSemiring A] [Module R A] [IsScalarTower R A A]
  [SMulCommClass R A A]

theorem mem_centralizer_iff {s : Set A} {z : A} : z ∈ NonUnitalSubalgebra.centralizer R s ↔ ∀ g ∈ s, g * z = z * g := Iff.rfl

