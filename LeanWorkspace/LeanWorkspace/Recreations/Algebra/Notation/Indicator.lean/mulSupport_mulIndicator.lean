import Mathlib

variable {α β M N : Type*}

variable [One M] [One N] {s t : Set α} {f g : α → M} {a : α}

theorem mulSupport_mulIndicator :
    Function.mulSupport (s.mulIndicator f) = s ∩ Function.mulSupport f := ext fun x => by simp [Function.mem_mulSupport, Set.mulIndicator_apply_eq_one]

