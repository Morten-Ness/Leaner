import Mathlib

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'} (e : Embedding c c')
  {C : Type*} [Category* C] [HasZeroMorphisms C] [HasZeroObject C]

variable {K K' : HomologicalComplex C c'} {L L' : HomologicalComplex C c}
  [e.IsRelIff]

variable (ψ : K ⟶ L.extend e)

theorem comm (i j : ι) :
    ComplexShape.Embedding.homRestrict.f ψ i ≫ L.d i j = K.d (e.f i) (e.f j) ≫ ComplexShape.Embedding.homRestrict.f ψ j := by
  dsimp [ComplexShape.Embedding.homRestrict.f]
  simp only [assoc, ← ψ.comm_assoc, L.extend_d_eq e rfl rfl, Iso.inv_hom_id, comp_id]

