import Mathlib

variable (R : Type u) [Ring R] [TopologicalSpace R]

theorem coe_of (M : Type v) [AddCommGroup M] [Module R M] [TopologicalSpace M] [ContinuousAdd M]
    [ContinuousSMul R M] : (of R M) = M := rfl

