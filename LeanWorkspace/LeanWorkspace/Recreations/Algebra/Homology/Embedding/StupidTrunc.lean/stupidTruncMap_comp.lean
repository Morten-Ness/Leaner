import Mathlib

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}

variable {C : Type*} [Category* C] [HasZeroMorphisms C] [HasZeroObject C]

variable (K L M : HomologicalComplex C c') (φ : K ⟶ L) (φ' : L ⟶ M)
  (e : c.Embedding c') [e.IsRelIff]

theorem stupidTruncMap_comp :
    HomologicalComplex.stupidTruncMap (φ ≫ φ') e = HomologicalComplex.stupidTruncMap φ e ≫ HomologicalComplex.stupidTruncMap φ' e := by
  simp [HomologicalComplex.stupidTruncMap, HomologicalComplex.stupidTrunc]

