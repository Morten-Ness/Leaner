import Mathlib

variable (C : Type*) [Category* C] [HasZeroMorphisms C] {ι : Type*} (c : ComplexShape ι)

variable (K L M : HomologicalComplex C c) (φ : K ⟶ L) (iso : K ≅ L) (ψ : L ⟶ M) (i j k : ι)

set_option backward.isDefEq.respectTransparency false in
theorem epi_homologyMap_of_epi_of_not_rel (φ : K ⟶ L) (i : ι)
    [K.HasHomology i] [L.HasHomology i] [Epi (φ.f i)] (hi : ∀ j, ¬ c.Rel i j) :
    Epi (HomologicalComplex.homologyMap φ i) := ((MorphismProperty.epimorphisms C).arrow_mk_iso_iff
    (Arrow.isoMk (K.isoHomologyι i _ rfl (shape _ _ _ (by tauto)))
      (L.isoHomologyι i _ rfl (shape _ _ _ (by tauto))))).2
      (MorphismProperty.epimorphisms.infer_property (HomologicalComplex.opcyclesMap φ i))

