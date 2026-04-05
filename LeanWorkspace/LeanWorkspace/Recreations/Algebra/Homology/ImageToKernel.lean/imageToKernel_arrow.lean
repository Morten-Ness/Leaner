import Mathlib

variable {ι : Type*}

variable {V : Type u} [Category.{v} V] [HasZeroMorphisms V]

variable {A B C : V} (f : A ⟶ B) [HasImage f] (g : B ⟶ C) [HasKernel g]

theorem imageToKernel_arrow (w : f ≫ g = 0) :
    imageToKernel f g w ≫ (kernelSubobject g).arrow = (imageSubobject f).arrow := by
  simp [imageToKernel]

-- This is less useful as a `simp` lemma than it initially appears,
-- as it "loses" the information the morphism factors through the image.

