import Mathlib

variable {C : Type u} [Category.{v} C] [Preadditive C] {R : Type*} [Ring R] [Linear R C]

variable {F G K L : CochainComplex C ℤ} (n m : ℤ)

theorem ofHom_homOf_eq_self (z : CochainComplex.HomComplex.Cocycle F G 0) : CochainComplex.HomComplex.Cocycle.ofHom (CochainComplex.HomComplex.Cocycle.homOf z) = z := by cat_disch

