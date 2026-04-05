import Mathlib

variable {ι : Type*}

variable {V : Type u} [Category.{v} V] [HasZeroMorphisms V]

variable {A B C : V} (f : A ⟶ B) (g : B ⟶ C) (w : f ≫ g = 0) [HasKernels V] [HasImages V]

theorem imageToKernel'_kernelSubobjectIso (w : f ≫ g = 0) :
    imageToKernel' f g w ≫ (kernelSubobjectIso g).inv =
      (imageSubobjectIso f).inv ≫ imageToKernel f g w := by
  ext
  simp [imageToKernel']

