import Mathlib

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  {C : Type*} [Category* C] [HasZeroMorphisms C]
  (K L : HomologicalComplex C c') (φ : K ⟶ L) (e : c.Embedding c') [e.IsTruncGE]
  [∀ i', K.HasHomology i'] [∀ i', L.HasHomology i']

variable (i j k : ι) (hi : c.prev j = i) (hk : c.next j = k)

variable {j' : ι'} (hj' : e.f j = j') (hj : e.BoundaryGE j)

theorem homologyι_truncGE'XIsoOpcycles_inv_d :
    (K.homologyι j' ≫ (K.truncGE'XIsoOpcycles e hj' hj).inv) ≫ (K.truncGE' e).d j k = 0 := by
  by_cases hjk : c.Rel j k
  · rw [K.truncGE'_d_eq_fromOpcycles e hjk hj' rfl hj, assoc, Iso.inv_hom_id_assoc,
    homologyι_comp_fromOpcycles_assoc, zero_comp]
  · rw [shape _ _ _ hjk, comp_zero]

