import Mathlib

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}

variable {C : Type*} [Category* C] [HasZeroObject C] [Preadditive C]
  {K L : HomologicalComplex C c} {f g : K ⟶ L}

theorem extend_ofExtend {e : c.Embedding c'} [e.IsRelIff]
    (h : Homotopy (extendMap f e) (extendMap g e)) :
    (Homotopy.ofExtend h).extend e = h := by
  ext i' j'
  by_cases hi' : ∃ i, e.f i = i'
  · obtain ⟨i, rfl⟩ := hi'
    by_cases hj' : ∃ j, e.f j = j'
    · obtain ⟨j, rfl⟩ := hj'
      simp [Homotopy.extend_hom_eq _ e rfl rfl, ofExtend_hom]
    · exact (isZero_extend_X _ _ _ (by tauto)).eq_of_tgt _ _
  · exact (isZero_extend_X _ _ _ (by tauto)).eq_of_src _ _

