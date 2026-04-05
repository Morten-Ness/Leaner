import Mathlib

variable (R : Type u) [CommRing R]

variable {Q : MorphismProperty CommRingCat.{u}}

theorem essentiallySmall_of_le (hQ : Q ≤ toMorphismProperty FiniteType) (R : CommRingCat.{u}) :
    EssentiallySmall.{u} (MorphismProperty.Under Q ⊤ R) := essentiallySmall_of_fully_faithful
    (MorphismProperty.Comma.changeProp _ _ hQ
      le_rfl le_rfl ⋙ (FGAlgCat.equivUnder R).inverse)

