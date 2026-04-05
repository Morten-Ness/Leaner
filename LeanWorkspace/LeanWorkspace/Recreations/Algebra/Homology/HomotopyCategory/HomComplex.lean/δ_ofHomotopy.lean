import Mathlib

variable {C : Type u} [Category.{v} C] [Preadditive C] {R : Type*} [Ring R] [Linear R C]

variable {F G K L : CochainComplex C ℤ} (n m : ℤ)

theorem δ_ofHomotopy {φ₁ φ₂ : F ⟶ G} (h : Homotopy φ₁ φ₂) :
    CochainComplex.HomComplex.δ (-1) 0 (CochainComplex.HomComplex.Cochain.ofHomotopy h) = CochainComplex.HomComplex.Cochain.ofHom φ₁ - CochainComplex.HomComplex.Cochain.ofHom φ₂ := by
  ext p
  have eq := h.comm p
  rw [dNext_eq h.hom (show (ComplexShape.up ℤ).Rel p (p + 1) by simp),
    prevD_eq h.hom (show (ComplexShape.up ℤ).Rel (p - 1) p by simp)] at eq
  rw [CochainComplex.HomComplex.Cochain.ofHomotopy, CochainComplex.HomComplex.δ_v (-1) 0 (neg_add_cancel 1) _ p p (add_zero p) (p - 1) (p + 1) rfl rfl]
  simp only [CochainComplex.HomComplex.Cochain.mk_v, one_smul, Int.negOnePow_zero, CochainComplex.HomComplex.Cochain.sub_v, CochainComplex.HomComplex.Cochain.ofHom_v, eq]
  abel

