import Mathlib

variable {C : Type u} [Category.{v} C] [Preadditive C] {R : Type*} [Ring R] [Linear R C]
  {K L M : CochainComplex C ℤ} {n : ℤ}

theorem equivHomShift_comp {K' : CochainComplex C ℤ}
    (g : K' ⟶ K) (f : K ⟶ L⟦n⟧) :
    CochainComplex.HomComplex.Cocycle.equivHomShift (g ≫ f) = CochainComplex.HomComplex.Cocycle.precomp (CochainComplex.HomComplex.Cocycle.equivHomShift f) g := by
  ext p q hpq
  simp [equivHomShift_apply, Cochain.rightUnshift_v _ _ _ _ _ _ _ (add_zero p)]

