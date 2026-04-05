import Mathlib

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  {C : Type*} [Category* C]

variable [HasZeroMorphisms C] (K L : HomologicalComplex C c') (φ : K ⟶ L) (e : c.Embedding c')
  [e.IsTruncLE] [∀ i', K.HasHomology i'] [∀ i', L.HasHomology i']

set_option backward.isDefEq.respectTransparency false in
theorem quasiIsoAt_truncLE'ToRestriction (j : ι) (hj : ¬ e.BoundaryLE j)
    [(K.restriction e).HasHomology j] [(K.truncLE' e).HasHomology j] :
    QuasiIsoAt (K.truncLE'ToRestriction e) j := by
  dsimp only [truncLE'ToRestriction]
  have : (K.op.restriction e.op).HasHomology j :=
    inferInstanceAs ((K.restriction e).op.HasHomology j)
  rw [quasiIsoAt_unopFunctor_map_iff]
  exact truncGE'.quasiIsoAt_restrictionToTruncGE' K.op e.op j (by simpa)

