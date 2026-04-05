import Mathlib

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  {C : Type*} [Category* C]

variable [HasZeroMorphisms C] (K L : HomologicalComplex C c') (φ : K ⟶ L) (e : c.Embedding c')
  [e.IsTruncLE] [∀ i', K.HasHomology i'] [∀ i', L.HasHomology i']

variable [HasZeroObject C]

theorem acyclic_truncLE_iff_isSupportedOutside :
    (K.truncLE e).Acyclic ↔ K.IsSupportedOutside e := by
  rw [← acyclic_op_iff, ← isSupportedOutside_op_iff]
  exact K.op.acyclic_truncGE_iff_isSupportedOutside e.op

