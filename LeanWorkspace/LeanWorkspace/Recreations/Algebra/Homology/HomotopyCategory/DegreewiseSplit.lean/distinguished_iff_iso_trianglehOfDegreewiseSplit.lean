import Mathlib

variable {C : Type*} [Category.{v} C] [Preadditive C]

variable [HasZeroObject C] [HasBinaryBiproducts C]

theorem distinguished_iff_iso_trianglehOfDegreewiseSplit
    (T : Triangle (HomotopyCategory C (ComplexShape.up ℤ))) :
    (T ∈ distTriang _) ↔ ∃ (S : ShortComplex (CochainComplex C ℤ))
      (σ : ∀ n, (S.map (HomologicalComplex.eval C _ n)).Splitting),
      Nonempty (T ≅ CochainComplex.trianglehOfDegreewiseSplit S σ) := by
  constructor
  · intro hT
    obtain ⟨K, L, φ, ⟨e⟩⟩ := inv_rot_of_distTriang _ hT
    exact ⟨_, _, ⟨(triangleRotation _).counitIso.symm.app _ ≪≫ (rotate _).mapIso e ≪≫
      CochainComplex.mappingCone.trianglehRotateIsoTrianglehOfDegreewiseSplit φ⟩⟩
  · rintro ⟨S, σ, ⟨e⟩⟩
    rw [rotate_distinguished_triangle, rotate_distinguished_triangle]
    refine isomorphic_distinguished _ ?_ _
      ((rotate _ ⋙ rotate _).mapIso e ≪≫
        CochainComplex.trianglehOfDegreewiseSplitRotateRotateIso S σ)
    exact ⟨_, _, _, ⟨Iso.refl _⟩⟩

