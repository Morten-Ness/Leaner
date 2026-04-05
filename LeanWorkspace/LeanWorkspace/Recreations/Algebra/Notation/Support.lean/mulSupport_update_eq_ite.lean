import Mathlib

variable {ι κ M N P : Type*}

variable [One M] [One N] [One P] {f g : ι → M} {s : Set ι} {x : ι}

theorem mulSupport_update_eq_ite [DecidableEq ι] [DecidableEq M] (f : ι → M) (x : ι) (y : M) :
    Function.mulSupport (Function.update f x y) = if y = 1 then Function.mulSupport f \ {x} else insert x (Function.mulSupport f) := by
  rcases eq_or_ne y 1 with rfl | hy <;> simp [Function.mulSupport_update_one, Function.mulSupport_update_of_ne_one, *]

