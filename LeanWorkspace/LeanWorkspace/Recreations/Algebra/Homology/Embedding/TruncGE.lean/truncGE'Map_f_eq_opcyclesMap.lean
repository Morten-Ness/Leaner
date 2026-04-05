import Mathlib

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  {C : Type*} [Category* C] [HasZeroMorphisms C]

variable (K L M : HomologicalComplex C c') (φ : K ⟶ L) (φ' : L ⟶ M)
  (e : c.Embedding c') [e.IsTruncGE]
  [∀ i', K.HasHomology i'] [∀ i', L.HasHomology i'] [∀ i', M.HasHomology i']

theorem truncGE'Map_f_eq_opcyclesMap {i : ι} (hi : e.BoundaryGE i) {i' : ι'} (h : e.f i = i') :
    (HomologicalComplex.truncGE'Map φ e).f i =
      (K.truncGE'XIsoOpcycles e h hi).hom ≫ opcyclesMap φ i' ≫
        (L.truncGE'XIsoOpcycles e h hi).inv := by
  subst h
  exact dif_pos hi

