import Mathlib

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  {C : Type*} [Category* C] [HasZeroMorphisms C]

variable (K L M : HomologicalComplex C c') (φ : K ⟶ L) (φ' : L ⟶ M)
  (e : c.Embedding c') [e.IsTruncLE]
  [∀ i', K.HasHomology i'] [∀ i', L.HasHomology i'] [∀ i', M.HasHomology i']

variable [HasZeroObject C]

theorem isIso_ιTruncLE_iff : IsIso (K.ιTruncLE e) ↔ K.IsStrictlySupported e := ⟨fun _ ↦ isStrictlySupported_of_iso (asIso (K.ιTruncLE e)) e,
    fun _ ↦ inferInstance⟩

