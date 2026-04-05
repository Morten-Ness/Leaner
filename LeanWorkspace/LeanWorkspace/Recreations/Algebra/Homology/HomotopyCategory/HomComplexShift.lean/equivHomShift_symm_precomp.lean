import Mathlib

variable {C : Type u} [Category.{v} C] [Preadditive C] {R : Type*} [Ring R] [Linear R C]
  {K L M : CochainComplex C ℤ} {n : ℤ}

theorem equivHomShift_symm_precomp
    (z : CochainComplex.HomComplex.Cocycle K L n) {K' : CochainComplex C ℤ} (g : K' ⟶ K) :
    CochainComplex.HomComplex.Cocycle.equivHomShift.symm (z.precomp g) = g ≫ CochainComplex.HomComplex.Cocycle.equivHomShift.symm z := CochainComplex.HomComplex.Cocycle.equivHomShift.injective (by simp [CochainComplex.HomComplex.Cocycle.equivHomShift_comp])

