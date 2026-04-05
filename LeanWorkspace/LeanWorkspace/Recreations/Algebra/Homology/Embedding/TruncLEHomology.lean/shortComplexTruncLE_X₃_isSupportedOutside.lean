import Mathlib

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  {C : Type*} [Category* C]

variable [Abelian C] (K : HomologicalComplex C c') (e : c.Embedding c') [e.IsTruncLE]

set_option backward.isDefEq.respectTransparency false in
theorem shortComplexTruncLE_X₃_isSupportedOutside :
    (K.shortComplexTruncLE e).X₃.IsSupportedOutside e where
  exactAt i := by
    rw [exactAt_iff_isZero_homology]
    by_cases hi : ∃ j', c'.Rel (e.f i) j'
    · obtain ⟨j', hj'⟩ := hi
      apply ((K.shortComplexTruncLE_shortExact e).homology_exact₃ (e.f i) j' hj').isZero_X₂
      · rw [← cancel_epi (homologyMap (K.ιTruncLE e) (e.f i)), comp_zero]
        dsimp [HomologicalComplex.shortComplexTruncLE]
        rw [← homologyMap_comp, cokernel.condition, homologyMap_zero]
      · simp
    · have : IsIso (homologyMap (K.shortComplexTruncLE e).f (e.f i)) := by dsimp; infer_instance
      rw [IsZero.iff_id_eq_zero, ← cancel_epi (homologyMap (K.shortComplexTruncLE e).g (e.f i)),
        comp_id, comp_zero, ← cancel_epi (homologyMap (K.shortComplexTruncLE e).f (e.f i)),
        comp_zero, ← homologyMap_comp, ShortComplex.zero, homologyMap_zero]

