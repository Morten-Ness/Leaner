import Mathlib

variable {C : Type u} [Category.{v} C] [Preadditive C] {R : Type*} [Ring R] [Linear R C]
  {K L M : CochainComplex C ℤ} {n : ℤ}

theorem equivHomShift_comp_shift (f : K ⟶ L⟦n⟧) {L' : CochainComplex C ℤ} (g : L ⟶ L') :
    CochainComplex.HomComplex.Cocycle.equivHomShift (f ≫ g⟦n⟧') = CochainComplex.HomComplex.Cocycle.postcomp (CochainComplex.HomComplex.Cocycle.equivHomShift f) g := by
  ext p q rfl
  simp [equivHomShift_apply, Cochain.rightUnshift_v _ _ _ _ _ _ _ (add_zero p)]

