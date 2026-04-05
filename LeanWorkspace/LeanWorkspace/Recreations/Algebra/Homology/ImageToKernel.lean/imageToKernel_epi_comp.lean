import Mathlib

variable {ι : Type*}

variable {V : Type u} [Category.{v} V] [HasZeroMorphisms V]

variable {A B C : V} (f : A ⟶ B) (g : B ⟶ C)

variable [HasKernels V] [HasImages V]

theorem imageToKernel_epi_comp {Z : V} (h : Z ⟶ A) [Epi h] (w) :
    imageToKernel (h ≫ f) g w =
      Subobject.ofLE _ _ (imageSubobject_comp_le h f) ≫
        imageToKernel f g ((cancel_epi h).mp (by simpa using w : h ≫ f ≫ g = h ≫ 0)) := by
  ext
  simp

