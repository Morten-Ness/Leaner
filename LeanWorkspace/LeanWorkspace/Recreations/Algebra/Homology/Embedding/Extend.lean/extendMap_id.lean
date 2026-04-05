import Mathlib

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}

variable {C : Type*} [Category* C] [HasZeroObject C]

variable [HasZeroMorphisms C] (K L M : HomologicalComplex C c)
  (φ : K ⟶ L) (φ' : L ⟶ M) (e : c.Embedding c')

theorem extendMap_id : HomologicalComplex.extendMap (𝟙 K) e = 𝟙 _ := by
  ext
  simpa using HomologicalComplex.extendMap_id_f _ _ _

