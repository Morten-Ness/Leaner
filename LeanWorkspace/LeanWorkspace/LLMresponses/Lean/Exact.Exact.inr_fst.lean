FAIL
import Mathlib

variable {R M M' N N' P P' : Type*}

variable [Semiring R] [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]

theorem Exact.inr_fst : Function.Exact (LinearMap.inr R M N) (LinearMap.fst R M N) := by
  rw [LinearMap.exact_iff]
  ext x
  constructor
  · intro hx
    refine ⟨x.2, ?_⟩
    apply Prod.ext
    · exact hx
    · simp [LinearMap.inr]
  · rintro ⟨y, rfl⟩
    rfl
