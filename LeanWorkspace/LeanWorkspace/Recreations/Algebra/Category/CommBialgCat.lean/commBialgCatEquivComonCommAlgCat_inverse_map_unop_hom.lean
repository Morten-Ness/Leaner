import Mathlib

open scoped MonoidalCategory

variable {R : Type u} [CommRing R]

theorem commBialgCatEquivComonCommAlgCat_inverse_map_unop_hom
    {A B : (Mon (CommAlgCat R)ᵒᵖ)ᵒᵖ} (f : A ⟶ B) :
  AlgHomClass.toAlgHom ((commBialgCatEquivComonCommAlgCat R).inverse.map f).hom =
    f.unop.hom.unop.hom := rfl

