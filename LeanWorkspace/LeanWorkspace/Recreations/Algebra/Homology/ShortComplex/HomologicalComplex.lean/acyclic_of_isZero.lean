import Mathlib

variable (C : Type*) [Category* C] [HasZeroMorphisms C] {ι : Type*} (c : ComplexShape ι)

variable (K L M : HomologicalComplex C c) (φ : K ⟶ L) (iso : K ≅ L) (ψ : L ⟶ M) (i j k : ι)

theorem acyclic_of_isZero (hK : IsZero K) :
    K.Acyclic := by
  rw [HomologicalComplex.acyclic_iff]
  intro i
  apply ShortComplex.exact_of_isZero_X₂
  exact (eval _ _ i).map_isZero hK

