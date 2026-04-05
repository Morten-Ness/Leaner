import Mathlib

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'} (e : Embedding c c')
  {C : Type*} [Category* C] [HasZeroMorphisms C] [HasZeroObject C]

variable {K K' : HomologicalComplex C c'} {L L' : HomologicalComplex C c}
  [e.IsRelIff]

theorem liftExtend_homRestrict (ψ : K ⟶ L.extend e) :
    e.liftExtend (e.homRestrict ψ) (ComplexShape.Embedding.homRestrict_hasLift e ψ) = ψ := by
  ext i'
  by_cases hi' : ∃ i, e.f i = i'
  · obtain ⟨i, rfl⟩ := hi'
    simp [ComplexShape.Embedding.homRestrict_f e _ rfl, ComplexShape.Embedding.liftExtend_f e _ _ rfl]
  · apply (L.isZero_extend_X e i' (by simpa using hi')).eq_of_tgt

