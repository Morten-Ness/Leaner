import Mathlib

variable {C : Type u} [Category.{v} C] [Preadditive C] {R : Type*} [Ring R] [Linear R C]

variable {F G K L : CochainComplex C ℤ} (n m : ℤ)

theorem ofHom_injective {f₁ f₂ : F ⟶ G} (h : CochainComplex.HomComplex.Cochain.ofHom f₁ = CochainComplex.HomComplex.Cochain.ofHom f₂) : f₁ = f₂ := (CochainComplex.HomComplex.Cocycle.equivHom F G).injective (by ext1; exact h)

