import Mathlib

variable {C : Type*} [Category* C] [Preadditive C]

variable {ι : Type*} {c : ComplexShape ι} {F G K : HomologicalComplex C c} (φ : F ⟶ G)

variable [HasHomotopyCofiber φ] [DecidableRel c.Rel]

variable [∀ i, HasBinaryBiproduct (K.X i) (K.X i)]
  [HasHomotopyCofiber (biprod.lift (𝟙 K) (-𝟙 K))]

variable (hc : ∀ j, ∃ i, c.Rel i j)

include hc in
theorem map_ι₀_eq_map_ι₁ {D : Type*} [Category* D] (H : HomologicalComplex C c ⥤ D)
    (hH : (homotopyEquivalences C c).IsInvertedBy H) :
    H.map (HomologicalComplex.cylinder.ι₀ K) = H.map (HomologicalComplex.cylinder.ι₁ K) := by
  have : IsIso (H.map (HomologicalComplex.cylinder.π K)) := hH _ ⟨HomologicalComplex.cylinder.homotopyEquiv K hc, rfl⟩
  simp only [← cancel_mono (H.map (HomologicalComplex.cylinder.π K)), ← H.map_comp, HomologicalComplex.cylinder.ι₀_π, H.map_id, HomologicalComplex.cylinder.ι₁_π]

