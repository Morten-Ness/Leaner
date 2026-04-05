import Mathlib

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}

variable {C : Type*} [Category* C] [HasZeroObject C]

theorem extendMap_add [Preadditive C] {K L : HomologicalComplex C c} (φ φ' : K ⟶ L)
    (e : c.Embedding c') : HomologicalComplex.extendMap (φ + φ' : K ⟶ L) e = HomologicalComplex.extendMap φ e + HomologicalComplex.extendMap φ' e := by
  ext i'
  by_cases hi' : ∃ i, e.f i = i'
  · obtain ⟨i, hi⟩ := hi'
    simp [HomologicalComplex.extendMap_f _ e hi]
  · apply (K.isZero_extend_X e i' (fun i hi => hi' ⟨i, hi⟩)).eq_of_src

