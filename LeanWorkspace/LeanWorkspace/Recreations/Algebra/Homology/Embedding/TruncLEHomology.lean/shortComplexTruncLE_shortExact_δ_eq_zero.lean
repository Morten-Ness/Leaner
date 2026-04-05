import Mathlib

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  {C : Type*} [Category* C]

variable [Abelian C] (K : HomologicalComplex C c') (e : c.Embedding c') [e.IsTruncLE]

set_option backward.isDefEq.respectTransparency false in
theorem shortComplexTruncLE_shortExact_δ_eq_zero (i' j' : ι') (hij' : c'.Rel i' j') :
    (K.shortComplexTruncLE_shortExact e).δ i' j' hij' = 0 := by
  by_cases hj : ∃ j, e.f j = j'
  · obtain ⟨j, rfl⟩ := hj
    rw [← cancel_mono (homologyMap (K.ιTruncLE e) (e.f j)), zero_comp]
    exact (K.shortComplexTruncLE_shortExact e).δ_comp i' _ hij'
  · apply ((K.truncLE e).exactAt_of_isSupported e j'
      (by simpa using hj)).isZero_homology.eq_of_tgt

