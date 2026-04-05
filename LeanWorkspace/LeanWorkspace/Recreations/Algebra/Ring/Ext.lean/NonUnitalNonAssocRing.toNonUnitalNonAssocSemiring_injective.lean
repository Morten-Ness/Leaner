import Mathlib

variable {R : Type u}

theorem toNonUnitalNonAssocSemiring_injective :
    Function.Injective (@toNonUnitalNonAssocSemiring R) := by
  intro _ _ h
  -- Use above extensionality lemma to prove injectivity by showing that `h_add` and `h_mul` hold.
  ext x y
  · exact congrArg (·.toAdd.add x y) h
  · exact congrArg (·.toMul.mul x y) h

