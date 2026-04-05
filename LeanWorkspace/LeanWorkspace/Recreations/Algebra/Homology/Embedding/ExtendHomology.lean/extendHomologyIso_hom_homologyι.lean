import Mathlib

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  {C : Type*} [Category* C] [HasZeroMorphisms C]
  [HasZeroObject C]

variable (K L M : HomologicalComplex C c) (φ : K ⟶ L) (φ' : L ⟶ M) (e : c.Embedding c')

variable {j : ι} {j' : ι'} (hj' : e.f j = j') [K.HasHomology j] [L.HasHomology j]
  [(K.extend e).HasHomology j'] [(L.extend e).HasHomology j']

theorem extendHomologyIso_hom_homologyι :
    (K.extendHomologyIso e hj').hom ≫ K.homologyι j =
      (K.extend e).homologyι j' ≫ (K.extendOpcyclesIso e hj').hom := by
  simp only [← cancel_epi ((K.extend e).homologyπ j'),
    homologyπ_extendHomologyIso_hom_assoc, homology_π_ι, extendCyclesIso_hom_iCycles_assoc,
    homology_π_ι_assoc, HomologicalComplex.pOpcycles_extendOpcyclesIso_hom]

