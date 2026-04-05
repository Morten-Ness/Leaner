import Mathlib

variable {ι : Type*}

variable {V : Type u} [Category.{v} V] [HasZeroMorphisms V]

variable {A B C : V} (f : A ⟶ B) (g : B ⟶ C)

theorem imageToKernel_zero_left [HasKernels V] [HasZeroObject V] {w} :
    imageToKernel (0 : A ⟶ B) g w = 0 := by
  ext
  simp

