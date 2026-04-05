import Mathlib

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  {C : Type*} [Category* C] [HasZeroMorphisms C]
  (K L : HomologicalComplex C c') (φ : K ⟶ L) (e : c.Embedding c') [e.IsTruncGE]
  [∀ i', K.HasHomology i'] [∀ i', L.HasHomology i']

variable [HasZeroObject C]

set_option backward.isDefEq.respectTransparency false in
theorem quasiIsoAt_πTruncGE {j : ι} {j' : ι'} (hj' : e.f j = j') :
    QuasiIsoAt (K.πTruncGE e) j' := by
  rw [quasiIsoAt_iff]
  by_cases hj : e.BoundaryGE j
  · rw [(truncGE.rightHomologyMapData K e hj' rfl rfl hj).quasiIso_iff]
    dsimp
    infer_instance
  · let φ := (shortComplexFunctor C c' j').map (K.πTruncGE e)
    have : Epi φ.τ₁ := by
      by_cases hi : ∃ i, e.f i = c'.prev j'
      · obtain ⟨i, hi⟩ := hi
        dsimp [φ, πTruncGE]
        rw [e.epi_liftExtend_f_iff _ _ hi]
        infer_instance
      · apply IsZero.epi (isZero_extend_X _ _ _ (by simpa using hi))
    have : IsIso φ.τ₂ := by
      dsimp [φ, πTruncGE]
      rw [e.isIso_liftExtend_f_iff _ _ hj']
      exact K.isIso_restrictionToTruncGE' e j hj
    have : IsIso φ.τ₃ := by
      dsimp [φ, πTruncGE]
      have : c'.next j' = e.f (c.next j) := by simpa only [← hj'] using e.next_f rfl
      rw [e.isIso_liftExtend_f_iff _ _ this.symm]
      exact K.isIso_restrictionToTruncGE' e _ (e.not_boundaryGE_next' hj rfl)
    exact ShortComplex.quasiIso_of_epi_of_isIso_of_mono φ

