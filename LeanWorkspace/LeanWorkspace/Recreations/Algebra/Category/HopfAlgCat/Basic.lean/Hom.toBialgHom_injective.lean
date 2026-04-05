import Mathlib

variable (R : Type u) [CommRing R]

theorem Hom.toBialgHom_injective (V W : HopfAlgCat.{v} R) :
    Function.Injective (Hom.toBialgHom : Hom V W → _) := fun ⟨f⟩ ⟨g⟩ _ => by congr

