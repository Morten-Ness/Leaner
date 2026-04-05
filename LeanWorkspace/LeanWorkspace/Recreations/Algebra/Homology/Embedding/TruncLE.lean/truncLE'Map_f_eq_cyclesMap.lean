import Mathlib

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  {C : Type*} [Category* C] [HasZeroMorphisms C]

variable (K L M : HomologicalComplex C c') (φ : K ⟶ L) (φ' : L ⟶ M)
  (e : c.Embedding c') [e.IsTruncLE]
  [∀ i', K.HasHomology i'] [∀ i', L.HasHomology i'] [∀ i', M.HasHomology i']

set_option backward.isDefEq.respectTransparency false in
theorem truncLE'Map_f_eq_cyclesMap {i : ι} (hi : e.BoundaryLE i) {i' : ι'} (h : e.f i = i') :
    (HomologicalComplex.truncLE'Map φ e).f i =
      (K.truncLE'XIsoCycles e h hi).hom ≫ cyclesMap φ i' ≫
        (L.truncLE'XIsoCycles e h hi).inv := by
  apply Quiver.Hom.op_inj
  dsimp [HomologicalComplex.truncLE'Map, HomologicalComplex.truncLE'XIsoCycles]
  rw [assoc, assoc, truncGE'Map_f_eq_opcyclesMap _ e.op (by simpa) h,
    opcyclesOpIso_inv_naturality_assoc, Iso.hom_inv_id_assoc]

