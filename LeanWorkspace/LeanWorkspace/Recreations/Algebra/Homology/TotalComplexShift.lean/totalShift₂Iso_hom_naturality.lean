import Mathlib

variable (C : Type*) [Category* C] [Preadditive C]

variable (K L : HomologicalComplex₂ C (up ℤ) (up ℤ)) (f : K ⟶ L)

variable (x y : ℤ) [K.HasTotal (up ℤ)]

set_option backward.isDefEq.respectTransparency false in
theorem totalShift₂Iso_hom_naturality [L.HasTotal (up ℤ)] :
    total.map ((shiftFunctor₂ C y).map f) (up ℤ) ≫ (L.totalShift₂Iso y).hom =
      (K.totalShift₂Iso y).hom ≫ (total.map f (up ℤ))⟦y⟧' := by
  ext n i₁ i₂ h
  dsimp at h ⊢
  rw [ιTotal_map_assoc, L.ι_totalShift₂Iso_hom_f y i₁ i₂ n h _ rfl _ rfl,
    K.ι_totalShift₂Iso_hom_f_assoc y i₁ i₂ n h _ rfl _ rfl]
  dsimp
  rw [id_comp, id_comp, comp_id, comp_id, Linear.comp_units_smul,
    Linear.units_smul_comp, ιTotal_map]

