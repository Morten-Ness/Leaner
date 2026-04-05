import Mathlib

variable {V : Type u} [Category.{v} V]

variable [HasZeroMorphisms V]

theorem truncateAugment_hom_f (C : ChainComplex V ℕ) {X : V} (f : C.X 0 ⟶ X) (w : C.d 1 0 ≫ f = 0)
    (i : ℕ) : (ChainComplex.truncateAugment C f w).hom.f i = 𝟙 (C.X i) := rfl

