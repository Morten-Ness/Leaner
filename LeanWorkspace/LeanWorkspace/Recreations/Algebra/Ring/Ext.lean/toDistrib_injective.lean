import Mathlib

variable {R : Type u}

theorem toDistrib_injective : Function.Injective (@toDistrib R) := by
  intro _ _ h
  ext x y
  · exact congrArg (·.toAdd.add x y) h
  · exact congrArg (·.toMul.mul x y) h

