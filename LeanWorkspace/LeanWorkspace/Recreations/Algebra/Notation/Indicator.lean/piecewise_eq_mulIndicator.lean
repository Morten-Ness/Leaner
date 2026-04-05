import Mathlib

variable {α β M N : Type*}

variable [One M] [One N] {s t : Set α} {f g : α → M} {a : α}

theorem piecewise_eq_mulIndicator [DecidablePred (· ∈ s)] : s.piecewise f 1 = s.mulIndicator f := funext fun _ => @if_congr _ _ _ _ (id _) _ _ _ _ Iff.rfl rfl rfl

