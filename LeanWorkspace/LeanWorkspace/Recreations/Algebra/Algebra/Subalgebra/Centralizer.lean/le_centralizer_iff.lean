import Mathlib

variable {R : Type*} [CommSemiring R]

variable {A : Type*} [Semiring A] [Algebra R A]

theorem le_centralizer_iff (S T : Subalgebra R A) : S ≤ centralizer R T ↔ T ≤ centralizer R S := ⟨fun h t ht _ hs ↦ (h hs t ht).symm, fun h s hs _ ht ↦ (h ht s hs).symm⟩

