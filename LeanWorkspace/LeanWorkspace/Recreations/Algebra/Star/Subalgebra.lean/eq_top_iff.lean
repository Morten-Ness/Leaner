import Mathlib

variable {F R A B : Type*} [CommSemiring R] [StarRing R]

variable [Semiring A] [Algebra R A] [StarRing A] [StarModule R A]

variable [Semiring B] [Algebra R B] [StarRing B] [StarModule R B]

theorem eq_top_iff {S : StarSubalgebra R A} : S = ⊤ ↔ ∀ x : A, x ∈ S := ⟨fun h x => by rw [h]; exact StarSubalgebra.mem_top,
  fun h => by StarSubalgebra.ext x; exact ⟨fun _ => StarSubalgebra.mem_top, fun _ => h x⟩⟩

