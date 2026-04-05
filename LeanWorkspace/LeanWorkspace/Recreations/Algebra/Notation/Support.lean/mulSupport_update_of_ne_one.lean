import Mathlib

variable {ι κ M N P : Type*}

variable [One M] [One N] [One P] {f g : ι → M} {s : Set ι} {x : ι}

theorem mulSupport_update_of_ne_one [DecidableEq ι] (f : ι → M) (x : ι) {y : M} (hy : y ≠ 1) :
    Function.mulSupport (Function.update f x y) = insert x (Function.mulSupport f) := by
  ext a; obtain rfl | hne := eq_or_ne a x <;> simp [*]

