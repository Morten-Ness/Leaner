import Mathlib

variable (C : Type*) [Category* C] [HasZeroMorphisms C] {ι : Type*} (c : ComplexShape ι)

variable (K L M : HomologicalComplex C c) (φ : K ⟶ L) (iso : K ≅ L) (ψ : L ⟶ M) (i j k : ι)

theorem ExactAt.of_iso (hK : K.ExactAt i) {L : HomologicalComplex C c} (e : K ≅ L) :
    L.ExactAt i := by
  rw [HomologicalComplex.exactAt_iff] at hK ⊢
  exact ShortComplex.exact_of_iso ((HomologicalComplex.shortComplexFunctor C c i).mapIso e) hK

