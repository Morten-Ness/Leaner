import Mathlib

variable {R S : CommRingCat.{u}}

theorem mkUnder_ext {A : Type u} [CommRing A] [Algebra R A] {B : Under R}
    {f g : CommRingCat.mkUnder R A ⟶ B} (h : ∀ a : A, f.right a = g.right a) :
    f = g := by
  ext x
  exact h x

