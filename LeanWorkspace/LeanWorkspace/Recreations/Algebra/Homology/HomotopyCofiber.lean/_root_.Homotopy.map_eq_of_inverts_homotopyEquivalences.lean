import Mathlib

variable {C : Type*} [Category* C] [Preadditive C]

variable {ι : Type*} {c : ComplexShape ι} {F G K : HomologicalComplex C c} (φ : F ⟶ G)

variable [HasHomotopyCofiber φ] [DecidableRel c.Rel]

variable [∀ i, HasBinaryBiproduct (K.X i) (K.X i)]
  [HasHomotopyCofiber (biprod.lift (𝟙 K) (-𝟙 K))]

omit [DecidableRel c.Rel] in
theorem _root_.Homotopy.map_eq_of_inverts_homotopyEquivalences
    {φ₀ φ₁ : F ⟶ G} (h : Homotopy φ₀ φ₁) (hc : ∀ j, ∃ i, c.Rel i j)
    [∀ i, HasBinaryBiproduct (F.X i) (F.X i)]
    [HasHomotopyCofiber (biprod.lift (𝟙 F) (-𝟙 F))]
    {D : Type*} [Category* D] (H : HomologicalComplex C c ⥤ D)
    (hH : (homotopyEquivalences C c).IsInvertedBy H) :
    H.map φ₀ = H.map φ₁ := by
  classical
  simp only [← HomologicalComplex.cylinder.ι₀_desc cylinder _ _ h, ← HomologicalComplex.cylinder.ι₁_desc cylinder _ _ h, H.map_comp,
    HomologicalComplex.cylinder.map_ι₀_eq_map_ι₁ cylinder _ hc _ hH]

