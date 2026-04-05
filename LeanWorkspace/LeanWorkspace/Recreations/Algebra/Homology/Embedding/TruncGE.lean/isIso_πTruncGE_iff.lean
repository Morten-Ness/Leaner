import Mathlib

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  {C : Type*} [Category* C] [HasZeroMorphisms C]

variable (K L M : HomologicalComplex C c') (φ : K ⟶ L) (φ' : L ⟶ M)
  (e : c.Embedding c') [e.IsTruncGE]
  [∀ i', K.HasHomology i'] [∀ i', L.HasHomology i'] [∀ i', M.HasHomology i']

variable [HasZeroObject C]

theorem isIso_πTruncGE_iff : IsIso (K.πTruncGE e) ↔ K.IsStrictlySupported e := ⟨fun _ ↦ isStrictlySupported_of_iso (asIso (K.πTruncGE e)).symm e,
    fun _ ↦ inferInstance⟩

