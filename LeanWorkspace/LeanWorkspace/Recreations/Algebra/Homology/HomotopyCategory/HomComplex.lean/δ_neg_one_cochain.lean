import Mathlib

variable {C : Type u} [Category.{v} C] [Preadditive C] {R : Type*} [Ring R] [Linear R C]

variable {F G K L : CochainComplex C ℤ} (n m : ℤ)

theorem δ_neg_one_cochain (z : CochainComplex.HomComplex.Cochain F G (-1)) :
    CochainComplex.HomComplex.δ (-1) 0 z = CochainComplex.HomComplex.Cochain.ofHom (Homotopy.nullHomotopicMap'
      (fun i j hij => z.v i j (by dsimp at hij; rw [← hij, add_neg_cancel_right]))) := by
  ext p
  rw [CochainComplex.HomComplex.δ_v (-1) 0 (neg_add_cancel 1) _ p p (add_zero p) (p - 1) (p + 1) rfl rfl]
  simp only [one_smul, CochainComplex.HomComplex.Cochain.ofHom_v, Int.negOnePow_zero]
  rw [Homotopy.nullHomotopicMap'_f (show (ComplexShape.up ℤ).Rel (p - 1) p by simp)
    (show (ComplexShape.up ℤ).Rel p (p + 1) by simp)]
  abel

