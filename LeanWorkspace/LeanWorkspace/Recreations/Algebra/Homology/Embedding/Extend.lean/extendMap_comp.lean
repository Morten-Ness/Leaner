import Mathlib

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}

variable {C : Type*} [Category* C] [HasZeroObject C]

variable [HasZeroMorphisms C] (K L M : HomologicalComplex C c)
  (φ : K ⟶ L) (φ' : L ⟶ M) (e : c.Embedding c')

theorem extendMap_comp :
    HomologicalComplex.extendMap (φ ≫ φ') e = HomologicalComplex.extendMap φ e ≫ HomologicalComplex.extendMap φ' e := by
  ext i'
  by_cases hi' : ∃ i, e.f i = i'
  · obtain ⟨i, hi⟩ := hi'
    simp [HomologicalComplex.extendMap_f _ e hi]
  · simp [HomologicalComplex.extendMap_f_eq_zero _ e i' (fun i hi => hi' ⟨i, hi⟩)]

