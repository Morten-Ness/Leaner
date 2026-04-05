import Mathlib

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  {C : Type*} [Category* C] [HasZeroMorphisms C]

variable (K L M : HomologicalComplex C c') (φ : K ⟶ L) (φ' : L ⟶ M)
  (e : c.Embedding c') [e.IsTruncLE]
  [∀ i', K.HasHomology i'] [∀ i', L.HasHomology i'] [∀ i', M.HasHomology i']

theorem isIso_truncLE'ToRestriction (i : ι) (hi : ¬ e.BoundaryLE i) :
    IsIso ((K.truncLE'ToRestriction e).f i) := by
  change IsIso ((K.op.restrictionToTruncGE' e.op).f i).unop
  have := K.op.isIso_restrictionToTruncGE' e.op i (by simpa)
  infer_instance

