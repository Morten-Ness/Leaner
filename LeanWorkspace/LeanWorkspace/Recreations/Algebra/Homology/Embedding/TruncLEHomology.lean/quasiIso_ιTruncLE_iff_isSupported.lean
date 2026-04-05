import Mathlib

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  {C : Type*} [Category* C]

variable [HasZeroMorphisms C] (K L : HomologicalComplex C c') (φ : K ⟶ L) (e : c.Embedding c')
  [e.IsTruncLE] [∀ i', K.HasHomology i'] [∀ i', L.HasHomology i']

variable [HasZeroObject C]

theorem quasiIso_ιTruncLE_iff_isSupported :
    QuasiIso (K.ιTruncLE e) ↔ K.IsSupported e := by
  rw [← quasiIso_opFunctor_map_iff, ← isSupported_op_iff]
  exact K.op.quasiIso_πTruncGE_iff_isSupported e.op

