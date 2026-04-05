import Mathlib

variable (C : Type*) [Category* C] [Preadditive C]

variable (K L : HomologicalComplex₂ C (up ℤ) (up ℤ)) (f : K ⟶ L)

variable (x y : ℤ) [K.HasTotal (up ℤ)]

set_option backward.isDefEq.respectTransparency false in
theorem totalShift₁Iso_trans_totalShift₂Iso :
    ((shiftFunctor₂ C y).obj K).totalShift₁Iso x ≪≫
      (shiftFunctor (CochainComplex C ℤ) x).mapIso (K.totalShift₂Iso y) =
    (x * y).negOnePow • (total.mapIso ((HomologicalComplex₂.shiftFunctor₁₂CommIso C x y).app K) (up ℤ)) ≪≫
      ((shiftFunctor₁ C x).obj K).totalShift₂Iso y ≪≫
      (shiftFunctor _ y).mapIso (K.totalShift₁Iso x) ≪≫
      (shiftFunctorComm (CochainComplex C ℤ) x y).app _ := by
  ext n n₁ n₂ h
  dsimp at h ⊢
  rw [Linear.comp_units_smul, ι_totalShift₁Iso_hom_f_assoc _ x n₁ n₂ n h _ rfl _ rfl,
    ιTotal_map_assoc, ι_totalShift₂Iso_hom_f_assoc _ y n₁ n₂ n h _ rfl _ rfl,
    Linear.units_smul_comp, Linear.comp_units_smul]
  dsimp [HomologicalComplex₂.shiftFunctor₁₂CommIso]
  rw [id_comp, id_comp, id_comp, id_comp, comp_id,
    HomologicalComplex₂.ι_totalShift₂Iso_hom_f _ y (n₁ + x) n₂ (n + x) (by lia) _ rfl _ rfl, smul_smul,
    ← Int.negOnePow_add, add_mul, add_comm (x * y)]
  dsimp
  rw [id_comp, comp_id,
    ι_totalShift₁Iso_hom_f_assoc _ x n₁ (n₂ + y) (n + y) (by lia) _ rfl (n + x + y) (by lia),
    CochainComplex.shiftFunctorComm_hom_app_f]
  dsimp
  rw [Iso.inv_hom_id, comp_id, id_comp]

