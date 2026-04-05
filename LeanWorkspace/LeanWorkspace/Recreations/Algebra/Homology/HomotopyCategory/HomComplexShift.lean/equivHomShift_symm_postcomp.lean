import Mathlib

variable {C : Type u} [Category.{v} C] [Preadditive C] {R : Type*} [Ring R] [Linear R C]
  {K L M : CochainComplex C ℤ} {n : ℤ}

theorem equivHomShift_symm_postcomp
    (z : CochainComplex.HomComplex.Cocycle K L n) {L' : CochainComplex C ℤ} (g : L ⟶ L') :
    CochainComplex.HomComplex.Cocycle.equivHomShift.symm (z.postcomp g) = CochainComplex.HomComplex.Cocycle.equivHomShift.symm z ≫ g⟦n⟧' := CochainComplex.HomComplex.Cocycle.equivHomShift.injective (by simp [CochainComplex.HomComplex.Cocycle.equivHomShift_comp_shift])

