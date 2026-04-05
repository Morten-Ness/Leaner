import Mathlib

open scoped MonoidalCategory

variable {R : Type u} [CommRing R]

theorem commBialgCatEquivComonCommAlgCat_functor_map_unop_hom {A B : CommBialgCat R} (f : A ⟶ B) :
  ((commBialgCatEquivComonCommAlgCat R).functor.map f).unop.hom =
    (CommAlgCat.ofHom (AlgHomClass.toAlgHom f.hom)).op := rfl

