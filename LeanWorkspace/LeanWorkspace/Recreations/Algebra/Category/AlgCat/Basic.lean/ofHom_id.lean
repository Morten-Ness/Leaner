import Mathlib

variable (R : Type u) [CommRing R]

theorem ofHom_id {X : Type v} [Ring X] [Algebra R X] : ofHom (AlgHom.id R X) = 𝟙 (of R X) := rfl

