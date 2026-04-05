import Mathlib

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}

variable {C : Type*} [Category* C] [HasZeroObject C] [Preadditive C]
  {K L : HomologicalComplex C c} {f g : K ⟶ L}

theorem ofExtend_extend (h : Homotopy f g) (e : c.Embedding c') [e.IsRelIff] :
    (h.extend e).ofExtend = h := by
  ext i j
  simp [ofExtend_hom, Homotopy.extend_hom_eq h e rfl rfl]

