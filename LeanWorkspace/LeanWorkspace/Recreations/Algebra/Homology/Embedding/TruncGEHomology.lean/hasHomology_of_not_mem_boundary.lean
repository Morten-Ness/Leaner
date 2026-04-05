import Mathlib

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  {C : Type*} [Category* C] [HasZeroMorphisms C]
  (K L : HomologicalComplex C c') (φ : K ⟶ L) (e : c.Embedding c') [e.IsTruncGE]
  [∀ i', K.HasHomology i'] [∀ i', L.HasHomology i']

variable (i j k : ι) (hi : c.prev j = i) (hk : c.next j = k)

theorem hasHomology_of_not_mem_boundary (hj : ¬ e.BoundaryGE j) :
    (K.truncGE' e).HasHomology j := HomologicalComplex.truncGE'.hasHomology_sc'_of_not_mem_boundary K e _ j _ rfl rfl hj

