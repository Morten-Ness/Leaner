import Mathlib

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}

variable {C : Type*} [Category* C] [HasZeroObject C] [Preadditive C]
  {K L : HomologicalComplex C c} {f g : K ⟶ L}

variable (e : c.Embedding c') (φ : ∀ i j, K.X i ⟶ L.X j)

theorem hom_eq_zero₂ (i' j' : ι') (hj' : ∀ j, e.f j ≠ j') :
    Homotopy.extend.hom e φ i' j' = 0 := (isZero_extend_X _ _ _ hj').eq_of_tgt _ _

