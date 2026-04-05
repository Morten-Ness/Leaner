import Mathlib

variable {G H : AddCommGrpCat.{0}} (f : G ⟶ H)

theorem image.lift_fac (F' : MonoFactorisation f) : AddCommGrpCat.image.lift F' ≫ F'.m = AddCommGrpCat.image.ι f := by
  ext x
  change (F'.e ≫ F'.m) _ = _
  rw [F'.fac, (Classical.indefiniteDescription _ x.2).2]
  rfl

