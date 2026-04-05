import Mathlib

variable {M : Type*} {N : Type*}

variable [MulOneClass M] {s : Set M}

variable [MulOneClass N]

theorem eq_of_eqOn_topM {f g : M →* N} (h : Set.EqOn f g (⊤ : Submonoid M)) : f = g := Submonoid.ext fun _ => h trivial

