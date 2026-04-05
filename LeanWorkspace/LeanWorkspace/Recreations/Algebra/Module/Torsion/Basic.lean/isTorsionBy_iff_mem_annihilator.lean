import Mathlib

variable (R M : Type*) [Semiring R] [AddCommMonoid M] [Module R M]

theorem isTorsionBy_iff_mem_annihilator {a : R} :
    IsTorsionBy R M a ↔ a ∈ annihilator R M := by
  rw [IsTorsionBy, mem_annihilator]

