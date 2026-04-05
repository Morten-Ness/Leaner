import Mathlib

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}

variable {C : Type*} [Category* C] [HasZeroObject C]

variable [HasZeroMorphisms C] [DecidableEq ι]
  (e : c.Embedding c') (X : C)

theorem extend_single_d (i : ι) (j' k' : ι') :
    (((single C c i).obj HomologicalComplex.extend.X).extend e).d j' k' = 0 := by
  by_cases hj : ∃ j, e.f j = j'
  · obtain ⟨j, rfl⟩ := hj
    by_cases hk : ∃ k, e.f k = k'
    · obtain ⟨k, rfl⟩ := hk
      simp [HomologicalComplex.extend_d_eq _ _ rfl rfl]
    · exact IsZero.eq_of_tgt (HomologicalComplex.isZero_extend_X _ _ _ (by tauto)) _ _
  · exact IsZero.eq_of_src (HomologicalComplex.isZero_extend_X _ _ _ (by tauto)) _ _

