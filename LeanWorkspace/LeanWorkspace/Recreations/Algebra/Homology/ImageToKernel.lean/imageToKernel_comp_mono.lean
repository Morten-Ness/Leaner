import Mathlib

variable {ι : Type*}

variable {V : Type u} [Category.{v} V] [HasZeroMorphisms V]

variable {A B C : V} (f : A ⟶ B) (g : B ⟶ C)

variable [HasKernels V] [HasImages V]

theorem imageToKernel_comp_mono {D : V} (h : C ⟶ D) [Mono h] (w) :
    imageToKernel f (g ≫ h) w =
      imageToKernel f g ((cancel_mono h).mp (by simpa using w : (f ≫ g) ≫ h = 0 ≫ h)) ≫
        (Subobject.isoOfEq _ _ (kernelSubobject_comp_mono g h)).inv := by
  ext
  simp

