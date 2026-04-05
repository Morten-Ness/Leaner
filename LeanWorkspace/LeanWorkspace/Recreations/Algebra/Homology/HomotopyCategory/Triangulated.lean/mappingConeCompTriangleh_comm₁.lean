import Mathlib

variable {C : Type*} [Category.{v} C] [Preadditive C] [HasBinaryBiproducts C]
  {X₁ X₂ X₃ : CochainComplex C ℤ} (f : X₁ ⟶ X₂) (g : X₂ ⟶ X₃)

set_option backward.isDefEq.respectTransparency false in
theorem mappingConeCompTriangleh_comm₁ :
    (CochainComplex.mappingConeCompTriangleh f g).mor₂ ≫
      (HomotopyCategory.quotient _ _).map (CochainComplex.mappingConeCompHomotopyEquiv f g).hom =
    (HomotopyCategory.quotient _ _).map (mappingCone.inr _) := by
  rw [← cancel_mono (HomotopyCategory.isoOfHomotopyEquiv
      (CochainComplex.mappingConeCompHomotopyEquiv f g)).inv, assoc]
  dsimp [CochainComplex.mappingConeCompTriangleh]
  rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp,
    CochainComplex.mappingConeCompHomotopyEquiv_hom_inv_id, comp_id,
    CochainComplex.mappingConeCompHomotopyEquiv_comm₁ f g,
    mappingConeCompTriangle_mor₂]

