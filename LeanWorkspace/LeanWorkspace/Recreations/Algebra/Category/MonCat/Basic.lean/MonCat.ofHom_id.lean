import Mathlib

theorem ofHom_id {M : Type u} [Monoid M] : ofHom (MonoidHom.id M) = 𝟙 (of M) := rfl

