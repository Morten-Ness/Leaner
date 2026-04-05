import Mathlib

variable {R M M' N N' P P' : Type*}

variable [Semiring R] [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]

theorem Exact.inl_snd : Function.Exact (LinearMap.inl R M N) (LinearMap.snd R M N) := by
  rintro ⟨x, y⟩
  simp only [LinearMap.snd_apply, @eq_comm _ y, LinearMap.coe_inl, Set.mem_range, Prod.mk.injEq,
    exists_eq_left]

