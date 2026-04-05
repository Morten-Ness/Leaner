import Mathlib

variable (R : Type u) [CommRing R]

theorem Hom.toCoalgHom_injective (V W : CoalgCat.{v} R) :
    Function.Injective (Hom.toCoalgHom' : Hom V W → _) := fun ⟨f⟩ ⟨g⟩ _ => by congr

