import Mathlib

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'} (e : Embedding c c')
  {C : Type*} [Category* C] [HasZeroMorphisms C] [HasZeroObject C]

variable {K K' : HomologicalComplex C c'} {L L' : HomologicalComplex C c}
  [e.IsRelIff]

variable (φ : K.restriction e ⟶ L) (hφ : e.HasLift φ)

variable {i' : ι'} {i : ι} (hi : e.f i = i')

theorem mono_liftExtend_f_iff (hi : e.f i = i') :
    Mono ((e.liftExtend φ hφ).f i') ↔ Mono (φ.f i) := (MorphismProperty.monomorphisms C).arrow_mk_iso_iff (e.liftExtendfArrowIso φ hφ hi)

