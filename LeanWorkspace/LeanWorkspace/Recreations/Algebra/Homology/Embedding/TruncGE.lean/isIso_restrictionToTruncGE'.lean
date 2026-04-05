import Mathlib

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  {C : Type*} [Category* C] [HasZeroMorphisms C]

variable (K L M : HomologicalComplex C c') (φ : K ⟶ L) (φ' : L ⟶ M)
  (e : c.Embedding c') [e.IsTruncGE]
  [∀ i', K.HasHomology i'] [∀ i', L.HasHomology i'] [∀ i', M.HasHomology i']

theorem isIso_restrictionToTruncGE' (i : ι) (hi : ¬ e.BoundaryGE i) :
    IsIso ((K.restrictionToTruncGE' e).f i) := by
  rw [K.restrictionToTruncGE'_f_eq_iso_hom_iso_inv e rfl hi]
  infer_instance

