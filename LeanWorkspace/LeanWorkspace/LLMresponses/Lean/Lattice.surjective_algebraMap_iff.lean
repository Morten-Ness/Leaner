FAIL
import Mathlib

variable (R : Type u) {A : Type v} {B : Type w}

variable [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

theorem surjective_algebraMap_iff :
    Function.Surjective (algebraMap R A) ↔ (⊤ : Subalgebra R A) = ⊥ := by
  constructor
  · intro h
    apply top_eq_bot_iff.mp
    intro x hx
    rcases h x with ⟨r, rfl⟩
    simp
  · intro h
    intro a
    refine ⟨0, ?_⟩
    have : a ∈ (⊥ : Subalgebra R A) := by
      rw [← h]
      simp
    simpa using this
