import Mathlib

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'} (e : Embedding c c')
  {C : Type*} [Category* C] [HasZeroMorphisms C] [HasZeroObject C]

variable {K K' : HomologicalComplex C c'} {L L' : HomologicalComplex C c}
  [e.IsRelIff]

set_option backward.isDefEq.respectTransparency false in
theorem homRestrict_hasLift (ψ : K ⟶ L.extend e) :
    e.HasLift (e.homRestrict ψ) := by
  intro j hj i' hij'
  have : (L.extend e).d i' (e.f j) = 0 := by
    apply (L.isZero_extend_X e i' (hj.notMem hij')).eq_of_src
  dsimp [ComplexShape.Embedding.homRestrict]
  rw [ComplexShape.Embedding.liftExtend.f_eq ComplexShape.Embedding.homRestrict ψ rfl, restrictionXIso, eqToIso_refl, Iso.refl_hom, id_comp,
    ← ψ.comm_assoc, this, zero_comp, comp_zero]

