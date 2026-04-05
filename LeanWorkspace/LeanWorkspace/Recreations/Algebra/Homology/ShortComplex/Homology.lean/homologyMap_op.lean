import Mathlib

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] (S : ShortComplex C)
  {S₁ S₂ S₃ S₄ : ShortComplex C}

variable (φ : S₁ ⟶ S₂) (h₁ : S₁.HomologyData) (h₂ : S₂.HomologyData)

set_option backward.isDefEq.respectTransparency false in
theorem homologyMap_op [HasHomology S₁] [HasHomology S₂] :
    (CategoryTheory.ShortComplex.homologyMap φ).op =
      (S₂.homologyOpIso).inv ≫ CategoryTheory.ShortComplex.homologyMap (opMap φ) ≫ (S₁.homologyOpIso).hom := by
  dsimp only [CategoryTheory.ShortComplex.homologyMap, CategoryTheory.ShortComplex.homologyOpIso]
  rw [CategoryTheory.ShortComplex.homologyMap'_op]
  dsimp only [Iso.symm, Iso.trans, Iso.op, Iso.refl, CategoryTheory.ShortComplex.rightHomologyIso, CategoryTheory.ShortComplex.leftHomologyIso,
    leftHomologyOpIso, leftHomologyMapIso', rightHomologyMapIso',
    LeftHomologyData.leftHomologyIso, CategoryTheory.ShortComplex.homologyMap']
  simp only [assoc, rightHomologyMap'_op, op_comp, ← leftHomologyMap'_comp_assoc, id_comp,
    opMap_id, comp_id, HomologyData.op_left]

