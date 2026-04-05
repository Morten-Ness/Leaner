import Mathlib

variable (R : Type u) [Semiring R]

theorem ofHom_id {M : Type v} [AddCommMonoid M] [Module R M] : ofHom LinearMap.id = 𝟙 (of R M) := rfl

