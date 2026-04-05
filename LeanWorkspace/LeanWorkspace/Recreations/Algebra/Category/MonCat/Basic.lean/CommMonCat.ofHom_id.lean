import Mathlib

theorem ofHom_id {M : Type u} [CommMonoid M] : ofHom (MonoidHom.id M) = 𝟙 (of M) := rfl

