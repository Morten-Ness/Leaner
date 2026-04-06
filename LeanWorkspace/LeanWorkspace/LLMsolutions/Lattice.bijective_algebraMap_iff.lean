FAIL
import Mathlib

variable (R : Type u) {A : Type v} {B : Type w}

variable [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

theorem bijective_algebraMap_iff {R A : Type*} [Field R] [Semiring A] [Nontrivial A]
    [Algebra R A] : Function.Bijective (algebraMap R A) ↔ (⊤ : Subalgebra R A) = ⊥ := by
  constructor
  · intro h
    apply le_antisymm
    · intro x hx
      rcases h.2 x with ⟨r, rfl⟩
      change algebraMap R A r = 0
      simp
    · exact bot_le
  · intro h
    constructor
    · exact FaithfulSMul.algebraMap_injective R A
    · intro x
      have hx : x = 0 := by
        have : x ∈ (⊤ : Subalgebra R A) := by simp
        rw [h] at this
        simpa using this
      refine ⟨0, ?_⟩
      simpa [hx]
