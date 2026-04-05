import Mathlib

variable {ι κ M N P : Type*}

variable [One M] [One N] [One P] {f g : ι → M} {s : Set ι} {x : ι}

theorem mulSupport_update_one [DecidableEq ι] (f : ι → M) (x : ι) :
    Function.mulSupport (Function.update f x 1) = Function.mulSupport f \ {x} := by
  ext a; obtain rfl | hne := eq_or_ne a x <;> simp [*]

