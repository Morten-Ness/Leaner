FAIL
import Mathlib

variable {R M M' N N' P P' : Type*}

variable [Semiring R] [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]

theorem Exact.inl_snd : Function.Exact (LinearMap.inl R M N) (LinearMap.snd R M N) := by
  rw [LinearMap.exact_iff]
  ext x
  constructor
  · rintro ⟨m, rfl⟩
    change LinearMap.snd R M N (LinearMap.inl R M N m) = 0
    simp
  · intro hx
    refine ⟨x.1, ?_⟩
    ext
    · simp [LinearMap.inl]
    · simpa [LinearMap.mem_ker] using hx
