import Mathlib

variable {C : Type u} [Category.{v} C] [Preadditive C] {R : Type*} [Ring R] [Linear R C]

variable {F G K L : CochainComplex C ℤ} (n m : ℤ)

theorem δ_comp_ofHom {n : ℤ} (z₁ : CochainComplex.HomComplex.Cochain F G n) (f : G ⟶ K) (m : ℤ) :
    CochainComplex.HomComplex.δ n m (z₁.comp (CochainComplex.HomComplex.Cochain.ofHom f) (add_zero n)) =
      (CochainComplex.HomComplex.δ n m z₁).comp (CochainComplex.HomComplex.Cochain.ofHom f) (add_zero m) := by
  rw [← CochainComplex.HomComplex.Cocycle.ofHom_coe, CochainComplex.HomComplex.δ_comp_zero_cocycle]

