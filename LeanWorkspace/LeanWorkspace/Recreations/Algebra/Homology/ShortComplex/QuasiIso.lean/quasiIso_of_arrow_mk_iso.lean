import Mathlib

variable {C : Type _} [Category* C] [HasZeroMorphisms C]
  {S₁ S₂ S₃ S₄ : ShortComplex C}
  [S₁.HasHomology] [S₂.HasHomology] [S₃.HasHomology] [S₄.HasHomology]

set_option backward.isDefEq.respectTransparency false in
theorem quasiIso_of_arrow_mk_iso (φ : S₁ ⟶ S₂) (φ' : S₃ ⟶ S₄) (e : Arrow.mk φ ≅ Arrow.mk φ')
    [hφ : QuasiIso φ] : QuasiIso φ' := by
  let α : S₃ ⟶ S₁ := e.inv.left
  let β : S₂ ⟶ S₄ := e.hom.right
  suffices φ' = α ≫ φ ≫ β by
    rw [this]
    infer_instance
  simp only [α, β, Arrow.w_mk_right_assoc, Arrow.mk_left, Arrow.mk_right, Arrow.mk_hom,
    ← Arrow.comp_right, e.inv_hom_id, Arrow.id_right, comp_id]

