import Mathlib

variable {C : Type u} [Category.{v} C] [Preadditive C] {R : Type*} [Ring R] [Linear R C]

variable {F G K L : CochainComplex C ℤ} (n m : ℤ)

theorem ofHom_zero : CochainComplex.HomComplex.Cochain.ofHom (0 : F ⟶ G) = 0 := by
  simp only [CochainComplex.HomComplex.Cochain.ofHom, HomologicalComplex.zero_f_apply, CochainComplex.HomComplex.Cochain.ofHoms_zero]

