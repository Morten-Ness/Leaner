import Mathlib

variable {V : Type u} [Category.{v} V]

variable [HasZeroMorphisms V]

theorem truncateAugment_hom_f (C : CochainComplex V ℕ) {X : V} (f : X ⟶ C.X 0)
    (w : f ≫ C.d 0 1 = 0) (i : ℕ) : (CochainComplex.truncateAugment C f w).hom.f i = 𝟙 (C.X i) := rfl

