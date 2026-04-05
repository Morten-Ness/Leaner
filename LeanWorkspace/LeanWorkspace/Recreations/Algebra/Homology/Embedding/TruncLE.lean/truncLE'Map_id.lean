import Mathlib

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  {C : Type*} [Category* C] [HasZeroMorphisms C]

variable (K L M : HomologicalComplex C c') (φ : K ⟶ L) (φ' : L ⟶ M)
  (e : c.Embedding c') [e.IsTruncLE]
  [∀ i', K.HasHomology i'] [∀ i', L.HasHomology i'] [∀ i', M.HasHomology i']

theorem truncLE'Map_id : HomologicalComplex.truncLE'Map (𝟙 K) e = 𝟙 _ := (unopFunctor C c.symm).congr_map (congr_arg Quiver.Hom.op (K.op.truncGE'Map_id e.op))

