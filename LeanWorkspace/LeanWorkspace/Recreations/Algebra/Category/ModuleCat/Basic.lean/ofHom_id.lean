import Mathlib

variable (R : Type u) [Ring R]

theorem ofHom_id {M : Type v} [AddCommGroup M] [Module R M] : ofHom LinearMap.id = 𝟙 (of R M) := rfl

