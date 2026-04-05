import Mathlib

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}

variable {C : Type*} [Category* C] [HasZeroMorphisms C] [HasZeroObject C]

variable (K L M : HomologicalComplex C c') (φ : K ⟶ L) (φ' : L ⟶ M)
  (e : c.Embedding c') [e.IsRelIff]

set_option backward.isDefEq.respectTransparency false in
theorem stupidTruncMap_stupidTruncXIso_hom {i : ι} {i' : ι'} (hi : e.f i = i') :
    (HomologicalComplex.stupidTruncMap φ e).f i' ≫ (L.stupidTruncXIso e hi).hom =
      (K.stupidTruncXIso e hi).hom ≫ φ.f i' := by
  subst hi
  simp [HomologicalComplex.stupidTruncMap, HomologicalComplex.stupidTruncXIso, extendMap_f _ _ rfl]

