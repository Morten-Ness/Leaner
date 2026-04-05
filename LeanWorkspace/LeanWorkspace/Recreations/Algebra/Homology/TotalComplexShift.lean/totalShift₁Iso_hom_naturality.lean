import Mathlib

variable (C : Type*) [Category* C] [Preadditive C]

variable (K L : HomologicalComplex₂ C (up ℤ) (up ℤ)) (f : K ⟶ L)

variable (x y : ℤ) [K.HasTotal (up ℤ)]

set_option backward.isDefEq.respectTransparency false in
theorem totalShift₁Iso_hom_naturality [L.HasTotal (up ℤ)] :
    total.map ((shiftFunctor₁ C x).map f) (up ℤ) ≫ (L.totalShift₁Iso x).hom =
      (K.totalShift₁Iso x).hom ≫ (total.map f (up ℤ))⟦x⟧' := by
  ext n i₁ i₂ h
  dsimp at h ⊢
  rw [ιTotal_map_assoc, L.ι_totalShift₁Iso_hom_f x i₁ i₂ n h _ rfl _ rfl,
    K.ι_totalShift₁Iso_hom_f_assoc x i₁ i₂ n h _ rfl _ rfl]
  dsimp
  rw [id_comp, id_comp, id_comp, comp_id, ιTotal_map]

