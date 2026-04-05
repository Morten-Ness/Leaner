import Mathlib

variable {C : Type u} [Category.{v} C] [Preadditive C] {R : Type*} [Ring R] [Linear R C]

variable {F G K L : CochainComplex C ℤ} (n m : ℤ)

theorem ofHomotopy_ofEq {φ₁ φ₂ : F ⟶ G} (h : φ₁ = φ₂) :
    CochainComplex.HomComplex.Cochain.ofHomotopy (Homotopy.ofEq h) = 0 := rfl

