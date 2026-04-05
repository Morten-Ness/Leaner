import Mathlib

variable {V : Type u} [Category.{v} V]

variable [HasZeroMorphisms V]

theorem truncateAugment_inv_f (C : ChainComplex V ℕ) {X : V} (f : C.X 0 ⟶ X) (w : C.d 1 0 ≫ f = 0)
    (i : ℕ) : (ChainComplex.truncateAugment C f w).inv.f i = 𝟙 ((ChainComplex.truncate.obj (ChainComplex.augment C f w)).X i) := rfl

