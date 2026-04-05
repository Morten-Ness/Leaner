import Mathlib

variable {R M M' N N' P P' : Type*}

variable [Semiring R] [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]

theorem Exact.inr_fst : Function.Exact (LinearMap.inr R M N) (LinearMap.fst R M N) := by
  rintro ⟨x, y⟩
  simp only [LinearMap.fst_apply, @eq_comm _ x, LinearMap.coe_inr, Set.mem_range, Prod.mk.injEq,
    exists_eq_right]

