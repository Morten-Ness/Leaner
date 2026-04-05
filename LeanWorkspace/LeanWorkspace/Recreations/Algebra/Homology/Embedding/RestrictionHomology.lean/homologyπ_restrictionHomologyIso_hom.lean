import Mathlib

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}

variable {C : Type*} [Category* C] [HasZeroMorphisms C]
  (K : HomologicalComplex C c') (e : c.Embedding c') [e.IsRelIff]

variable (i j k : ι) (hi : c.prev j = i) (hk : c.next j = k)
  {i' j' k' : ι'} (hi' : e.f i = i') (hj' : e.f j = j') (hk' : e.f k = k')
  (hi'' : c'.prev j' = i') (hk'' : c'.next j' = k')
  [K.HasHomology j'] [(K.restriction e).HasHomology j]

set_option backward.isDefEq.respectTransparency false in
theorem homologyπ_restrictionHomologyIso_hom :
    (K.restriction e).homologyπ j ≫
      (K.restrictionHomologyIso e i j k hi hk hi' hj' hk' hi'' hk'').hom =
    (K.restrictionCyclesIso e j k hk hj' hk' hk'').hom ≫ K.homologyπ j' := by
  have : ((K.restriction e).sc' i j k).HasHomology := by subst hi hk; assumption
  have : (K.sc' i' j' k').HasHomology := by subst hi'' hk''; assumption
  dsimp [HomologicalComplex.restrictionHomologyIso, homologyIsoSc']
  rw [← ShortComplex.homologyMap_comp, ← ShortComplex.homologyMap_comp,
    ← cancel_mono (K.sc j').homologyι, assoc, assoc]
  apply (ShortComplex.π_homologyMap_ι _).trans
  dsimp
  rw [comp_id, id_comp]
  apply (K.restrictionCyclesIso_hom_iCycles_assoc e j k hk hj' hk' hk'' _).symm.trans
  congr 1
  symm
  apply ShortComplex.homology_π_ι

