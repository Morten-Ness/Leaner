import Mathlib

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  {C : Type*} [Category* C] [HasZeroMorphisms C]
  (K L : HomologicalComplex C c') (φ : K ⟶ L) (e : c.Embedding c') [e.IsTruncGE]
  [∀ i', K.HasHomology i'] [∀ i', L.HasHomology i']

variable [HasZeroObject C]

theorem quasiIso_πTruncGE_iff_isSupported :
    QuasiIso (K.πTruncGE e) ↔ K.IsSupported e := by
  constructor
  · intro
    refine ⟨fun i' hi' => ?_⟩
    rw [exactAt_iff_of_quasiIsoAt (K.πTruncGE e) i']
    exact (K.truncGE e).exactAt_of_isSupported e i' hi'
  · intro
    rw [quasiIso_iff]
    intro i'
    by_cases hi' : ∃ i, e.f i = i'
    · obtain ⟨i, rfl⟩ := hi'
      infer_instance
    · rw [quasiIsoAt_iff_exactAt (K.πTruncGE e) i']
      all_goals exact exactAt_of_isSupported _ e i' (by simpa using hi')

