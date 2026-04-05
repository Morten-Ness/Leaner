import Mathlib

variable (R : Type u) {A : Type v} {B : Type w}

variable [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

theorem eq_top_iff {S : Subalgebra R A} : S = ⊤ ↔ ∀ x : A, x ∈ S := ⟨fun h x => by rw [h]; exact Algebra.mem_top, fun h => by
    ext x; exact ⟨fun _ => Algebra.mem_top, fun _ => h x⟩⟩

