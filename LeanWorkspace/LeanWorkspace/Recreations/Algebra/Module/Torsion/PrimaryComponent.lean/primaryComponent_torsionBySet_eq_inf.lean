import Mathlib

variable {A M M₁ M₂ : Type*} [CommRing A]

variable (I : Ideal A)

variable [AddCommMonoid M] [AddCommMonoid M₁] [AddCommMonoid M₂] [Module A M] [Module A M₁]
    [Module A M₂]

theorem primaryComponent_torsionBySet_eq_inf (I : Ideal A) :
    (Ideal.primaryComponent (torsionBySet A M ↑I) I).map (Submodule.subtype _) =
    Ideal.primaryComponent M I ⊓ torsionBySet A M ↑I := by
  ext x
  simp [Ideal.primaryComponent_mem]

