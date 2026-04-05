import Mathlib

variable {C : Type u} [Category.{v} C] [Preadditive C] {R : Type*} [Ring R] [Linear R C]

variable {F G K L : CochainComplex C ℤ} (n m : ℤ)

theorem cochain_ofHom_homOf_eq_coe (z : CochainComplex.HomComplex.Cocycle F G 0) :
    CochainComplex.HomComplex.Cochain.ofHom (CochainComplex.HomComplex.Cocycle.homOf z) = (z : CochainComplex.HomComplex.Cochain F G 0) := by
  simpa only [CochainComplex.HomComplex.Cocycle.ext_iff] using CochainComplex.HomComplex.Cocycle.ofHom_homOf_eq_self z

