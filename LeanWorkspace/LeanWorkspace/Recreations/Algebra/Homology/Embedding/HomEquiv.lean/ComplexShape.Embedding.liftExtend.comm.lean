import Mathlib

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'} (e : Embedding c c')
  {C : Type*} [Category* C] [HasZeroMorphisms C] [HasZeroObject C]

variable {K K' : HomologicalComplex C c'} {L L' : HomologicalComplex C c}
  [e.IsRelIff]

variable (φ : K.restriction e ⟶ L)

set_option backward.isDefEq.respectTransparency false in
theorem comm (hφ : e.HasLift φ) (i' j' : ι') :
    ComplexShape.Embedding.liftExtend.f φ i' ≫ (L.extend e).d i' j' = K.d i' j' ≫ ComplexShape.Embedding.liftExtend.f φ j' := by
  by_cases hij' : c'.Rel i' j'
  · by_cases hi' : ∃ i, e.f i = i'
    · obtain ⟨i, hi⟩ := hi'
      rw [ComplexShape.Embedding.liftExtend.f_eq φ hi]
      by_cases hj' : ∃ j, e.f j = j'
      · obtain ⟨j, hj⟩ := hj'
        rw [ComplexShape.Embedding.liftExtend.f_eq φ hj, L.extend_d_eq e hi hj]
        subst hi hj
        simp [HomologicalComplex.restrictionXIso]
      · apply (L.isZero_extend_X e j' (by simpa using hj')).eq_of_tgt
    · have : (L.extend e).d i' j' = 0 := by
        apply (L.isZero_extend_X e i' (by simpa using hi')).eq_of_src
      rw [this, comp_zero]
      by_cases hj' : ∃ j, e.f j = j'
      · obtain ⟨j, rfl⟩ := hj'
        rw [ComplexShape.Embedding.liftExtend.f_eq φ rfl]
        dsimp [restrictionXIso]
        rw [id_comp, reassoc_of% (hφ j (e.boundaryGE hij'
          (by simpa using hi')) i' hij'), zero_comp]
      · have : ComplexShape.Embedding.liftExtend.f φ j' = 0 := by
          apply (L.isZero_extend_X e j' (by simpa using hj')).eq_of_tgt
        rw [this, comp_zero]
  · simp [HomologicalComplex.shape _ _ _ hij']

