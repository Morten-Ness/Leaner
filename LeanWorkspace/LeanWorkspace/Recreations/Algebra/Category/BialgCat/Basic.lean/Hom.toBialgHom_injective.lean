import Mathlib

variable (R : Type u) [CommRing R]

theorem Hom.toBialgHom_injective (V W : BialgCat.{v} R) :
    Function.Injective (Hom.toBialgHom : Hom V W → _) := fun ⟨f⟩ ⟨g⟩ _ => by congr

-- TODO: if `Quiver.Hom` and the instance above were `reducible`, this wouldn't be needed.

