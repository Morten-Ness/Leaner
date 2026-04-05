import Mathlib

variable {C : Type u} [Category.{v} C] [Preadditive C] {R : Type*} [Ring R] [Linear R C]

variable {F G K L : CochainComplex C ℤ} (n m : ℤ)

theorem homOf_ofHom_eq_self (φ : F ⟶ G) : CochainComplex.HomComplex.Cocycle.homOf (CochainComplex.HomComplex.Cocycle.ofHom φ) = φ := by cat_disch

