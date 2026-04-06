import Mathlib

variable (R : Type u) {A : Type v} {B : Type w}

variable [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

theorem toSubring_bot (A : Type*) [CommRing A] (R : Subring A) :
    (⊥ : Subalgebra R A).toSubring = R := by
  ext x
  constructor
  · intro hx
    change x ∈ Set.range (algebraMap R A) at hx
    rcases hx with ⟨r, rfl⟩
    exact r.2
  · intro hx
    change x ∈ Set.range (algebraMap R A)
    refine ⟨⟨x, hx⟩, ?_⟩
    rfl
