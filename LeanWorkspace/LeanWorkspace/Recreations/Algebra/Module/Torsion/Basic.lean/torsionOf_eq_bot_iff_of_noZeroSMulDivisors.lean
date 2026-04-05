import Mathlib

variable (R M : Type*) [Semiring R] [AddCommMonoid M] [Module R M]

theorem torsionOf_eq_bot_iff_of_noZeroSMulDivisors [IsDomain R] [Module.IsTorsionFree R M] (m : M) :
    Ideal.torsionOf R M m = ⊥ ↔ m ≠ 0 := by
  refine ⟨fun h contra => ?_, fun h => (Submodule.eq_bot_iff _).mpr fun r hr => ?_⟩
  · rw [contra, Ideal.torsionOf_zero] at h
    exact bot_ne_top.symm h
  · rw [Ideal.mem_torsionOf_iff, smul_eq_zero] at hr
    tauto

