import Mathlib

variable {C : Type u} [Category.{v} C] [Preadditive C] {R : Type*} [Ring R] [Linear R C]

variable {F G K L : CochainComplex C ℤ} (n m : ℤ)

theorem δ_ofHom {p : ℤ} (φ : F ⟶ G) : CochainComplex.HomComplex.δ 0 p (CochainComplex.HomComplex.Cochain.ofHom φ) = 0 := by
  by_cases h : p = 1
  · subst h
    ext
    simp
  · rw [CochainComplex.HomComplex.δ_shape]
    lia

