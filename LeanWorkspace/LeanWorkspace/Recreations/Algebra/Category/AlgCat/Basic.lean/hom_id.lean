import Mathlib

variable (R : Type u) [CommRing R]

theorem hom_id {A : AlgCat.{v} R} : (𝟙 A : A ⟶ A).hom = AlgHom.id R A := rfl

