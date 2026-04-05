import Mathlib

variable {ι : Type*}

variable {V : Type u} [Category.{v} V] [HasZeroMorphisms V]

variable {A B C : V} (f : A ⟶ B) (g : B ⟶ C)

theorem imageToKernel_comp_hom_inv_comp [HasEqualizers V] [HasImages V] {Z : V} {i : B ≅ Z} (w) :
    imageToKernel (f ≫ i.hom) (i.inv ≫ g) w =
      (imageSubobjectCompIso _ _).hom ≫
        imageToKernel f g (by simpa using w) ≫ (kernelSubobjectIsoComp i.inv g).inv := by
  ext
  simp

