import Mathlib

variable {ι α : Type*}

variable {I : Type u}

variable {f : I → Type v} {M : ι → Type*}

variable (i : I)

theorem update_one [∀ i, One (f i)] [DecidableEq I] (i : I) : Function.update (1 : ∀ i, f i) i 1 = 1 := update_eq_self i (1 : (a : I) → f a)

