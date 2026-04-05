import Mathlib

variable {C : Type u} [Category.{v} C] [Preadditive C] {R : Type*} [Ring R] [Linear R C]

variable {F G K L : CochainComplex C ℤ} (n m : ℤ)

theorem ofHom_add (φ₁ φ₂ : F ⟶ G) :
    CochainComplex.HomComplex.Cochain.ofHom (φ₁ + φ₂) = CochainComplex.HomComplex.Cochain.ofHom φ₁ + CochainComplex.HomComplex.Cochain.ofHom φ₂ := by cat_disch

