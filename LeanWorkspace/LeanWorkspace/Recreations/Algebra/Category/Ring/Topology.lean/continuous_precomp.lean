import Mathlib

variable {R A B C : CommRingCat.{u}} [TopologicalSpace R]

theorem continuous_precomp (f : A ⟶ B) :
    Continuous ((f ≫ ·) : (B ⟶ R) → (A ⟶ R)) := continuous_induced_rng.mpr ((Pi.continuous_precomp f.hom).comp continuous_induced_dom)

