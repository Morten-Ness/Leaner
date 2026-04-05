import Mathlib

variable (R : Type u) {A : Type v} {B : Type w}

variable [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

theorem bijective_algebraMap_iff {R A : Type*} [Field R] [Semiring A] [Nontrivial A]
    [Algebra R A] : Function.Bijective (algebraMap R A) ↔ (⊤ : Subalgebra R A) = ⊥ := ⟨fun h => Algebra.surjective_algebraMap_iff.1 h.2, fun h =>
    ⟨(algebraMap R A).injective, Algebra.surjective_algebraMap_iff.2 h⟩⟩

