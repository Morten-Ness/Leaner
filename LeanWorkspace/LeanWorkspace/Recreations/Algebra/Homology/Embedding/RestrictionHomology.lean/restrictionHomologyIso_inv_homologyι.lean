import Mathlib

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}

variable {C : Type*} [Category* C] [HasZeroMorphisms C]
  (K : HomologicalComplex C c') (e : c.Embedding c') [e.IsRelIff]

variable (i j k : ι) (hi : c.prev j = i) (hk : c.next j = k)
  {i' j' k' : ι'} (hi' : e.f i = i') (hj' : e.f j = j') (hk' : e.f k = k')
  (hi'' : c'.prev j' = i') (hk'' : c'.next j' = k')
  [K.HasHomology j'] [(K.restriction e).HasHomology j]

set_option backward.isDefEq.respectTransparency false in
theorem restrictionHomologyIso_inv_homologyι :
    (K.restrictionHomologyIso e i j k hi hk hi' hj' hk' hi'' hk'').inv ≫
      (K.restriction e).homologyι j =
    K.homologyι j' ≫ (K.restrictionOpcyclesIso e i j hi hi' hj' hi'').inv := by
  have : ((K.restriction e).sc' i j k).HasHomology := by subst hi hk; assumption
  have : (K.sc' i' j' k').HasHomology := by subst hi'' hk''; assumption
  dsimp [HomologicalComplex.restrictionHomologyIso, homologyIsoSc']
  rw [← ShortComplex.homologyMap_comp, ← ShortComplex.homologyMap_comp, assoc,
    ← cancel_epi (K.sc j').homologyπ]
  apply (ShortComplex.π_homologyMap_ι _).trans
  dsimp
  rw [comp_id, id_comp]
  refine ((ShortComplex.homology_π_ι_assoc _ _).trans ?_).symm
  congr 1
  apply HomologicalComplex.pOpcycles_restrictionOpcyclesIso_inv

