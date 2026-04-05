import Mathlib

variable {C : Type u} [Category.{v} C] [Preadditive C] {R : Type*} [Ring R] [Linear R C]

variable {F G K L : CochainComplex C ℤ} (n m : ℤ)

theorem ofHom_comp (f : F ⟶ G) (g : G ⟶ K) :
    CochainComplex.HomComplex.Cochain.ofHom (f ≫ g) = (CochainComplex.HomComplex.Cochain.ofHom f).comp (CochainComplex.HomComplex.Cochain.ofHom g) (zero_add 0) := by
  simp only [CochainComplex.HomComplex.Cochain.ofHom, HomologicalComplex.comp_f, CochainComplex.HomComplex.Cochain.ofHoms_comp]

