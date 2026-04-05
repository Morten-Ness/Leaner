import Mathlib

variable {C : Type u} [Category.{v} C] [Preadditive C] {R : Type*} [Ring R] [Linear R C]

variable {F G K L : CochainComplex C ℤ} (n m : ℤ)

theorem equivHomotopy_apply_of_eq {φ₁ φ₂ : F ⟶ G} (h : φ₁ = φ₂) :
    (CochainComplex.HomComplex.Cochain.equivHomotopy _ _ (Homotopy.ofEq h)).1 = 0 := rfl

