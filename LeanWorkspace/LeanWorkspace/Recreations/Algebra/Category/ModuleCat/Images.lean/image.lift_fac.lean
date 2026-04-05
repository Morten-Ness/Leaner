import Mathlib

variable {R : Type u} [Ring R]

variable {G H : ModuleCat.{v} R} (f : G ⟶ H)

theorem image.lift_fac (F' : MonoFactorisation f) : ModuleCat.image.lift F' ≫ F'.m = ModuleCat.image.ι f := by
  ext x
  change (F'.e ≫ F'.m) _ = _
  rw [F'.fac, (Classical.indefiniteDescription _ x.2).2]
  rfl

