import Mathlib

variable (R G : Type*) [CommRing R] [Group G] [TopologicalSpace R]

variable [TopologicalSpace G] [IsTopologicalGroup G]

theorem Iobj_ρ_apply (rep : Action (TopModuleCat R) G) (g f x) :
    ((Iobj rep).ρ g).hom f x = (rep.ρ g).hom (f (g⁻¹ * x)) := rfl

