import Mathlib

variable {M : Type*} {N : Type*}

variable [Mul M] {s : Set M}

variable [Mul N]

theorem eq_of_eqOn_top {f g : M →ₙ* N} (h : Set.EqOn f g (⊤ : Subsemigroup M)) : f = g := Subsemigroup.ext fun _ => h trivial

