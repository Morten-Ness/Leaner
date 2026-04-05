import Mathlib

variable {C : Type u} [Category.{v} C] [Preadditive C] {R : Type*} [Ring R] [Linear R C]

variable {F G K L : CochainComplex C ℤ} (n m : ℤ)

theorem ofHom_v (φ : F ⟶ G) (p : ℤ) : (CochainComplex.HomComplex.Cochain.ofHom φ).v p p (add_zero p) = φ.f p := by
  simp only [CochainComplex.HomComplex.Cochain.ofHom, CochainComplex.HomComplex.Cochain.ofHoms_v]

