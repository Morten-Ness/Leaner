import Mathlib

variable {C : Type*} [Category* C] [Preadditive C]
  {I₁ I₂ I₁₂ : Type*} {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂}
  (K L M : HomologicalComplex₂ C c₁ c₂) (φ : K ⟶ L) (e : K ≅ L) (ψ : L ⟶ M)
  (c₁₂ : ComplexShape I₁₂) [TotalComplexShape c₁ c₂ c₁₂]

include e in
theorem hasTotal_of_iso [K.HasTotal c₁₂] : L.HasTotal c₁₂ := GradedObject.hasMap_of_iso (GradedObject.isoMk K.toGradedObject L.toGradedObject
    (fun ⟨i₁, i₂⟩ =>
      (HomologicalComplex.eval _ _ i₁ ⋙ HomologicalComplex.eval _ _ i₂).mapIso e)) _

