import Mathlib

variable {R : Type u}

theorem toNonAssocSemiring_injective :
    Function.Injective (@toNonAssocSemiring R) := by
  intro _ _ h
  ext x y
  · exact congrArg (·.toAdd.add x y) h
  · exact congrArg (·.toMul.mul x y) h

