import Mathlib

variable {C : Type*} [Category.{v} C] [Preadditive C] [HasBinaryBiproducts C]
  {X₁ X₂ X₃ : CochainComplex C ℤ} (f : X₁ ⟶ X₂) (g : X₂ ⟶ X₃)

variable [HasZeroObject C]

set_option backward.isDefEq.respectTransparency false in
theorem mappingConeCompTriangleh_distinguished :
    (CochainComplex.mappingConeCompTriangleh f g) ∈
      distTriang (HomotopyCategory C (ComplexShape.up ℤ)) := by
  refine ⟨_, _, (CochainComplex.mappingConeCompTriangle f g).mor₁, ⟨?_⟩⟩
  refine Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (isoOfHomotopyEquiv
    (CochainComplex.mappingConeCompHomotopyEquiv f g)) (by cat_disch) (by simp) ?_
  dsimp [CochainComplex.mappingConeCompTriangleh]
  rw [CategoryTheory.Functor.map_id, comp_id, ← Functor.map_comp_assoc]
  congr 2
  exact (CochainComplex.mappingConeCompHomotopyEquiv_comm₂ f g).symm

