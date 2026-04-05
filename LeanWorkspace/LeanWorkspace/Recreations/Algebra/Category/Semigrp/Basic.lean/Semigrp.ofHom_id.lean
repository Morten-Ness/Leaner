import Mathlib

theorem ofHom_id {X : Type u} [Semigroup X] : ofHom (MulHom.id X) = 𝟙 (of X) := rfl

