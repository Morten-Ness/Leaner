import Mathlib

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  {C : Type*} [Category* C] [HasZeroMorphisms C]

variable (K L M : HomologicalComplex C c') (φ : K ⟶ L) (φ' : L ⟶ M)
  (e : c.Embedding c') [e.IsTruncGE]
  [∀ i', K.HasHomology i'] [∀ i', L.HasHomology i'] [∀ i', M.HasHomology i']

theorem d_comp_d (i j k : ι) : HomologicalComplex.truncGE'.d K e i j ≫ HomologicalComplex.truncGE'.d K e j k = 0 := by
  dsimp [HomologicalComplex.truncGE'.d]
  by_cases hij : c.Rel i j
  · by_cases hjk : c.Rel j k
    · rw [dif_pos hij, dif_pos hjk, dif_neg (e.not_boundaryGE_next hij)]
      split_ifs <;> simp
    · rw [dif_neg hjk, comp_zero]
  · rw [dif_neg hij, zero_comp]

