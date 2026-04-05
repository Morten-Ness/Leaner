import Mathlib

variable {M : Type*} {N : Type*}

variable {A : Type*}

variable [MulOneClass M] {s : Set M}

variable [AddZeroClass A] {t : Set A}

variable (S : Submonoid M)

variable {t : Set M}

theorem closure_sdiff_singleton_one (s : Set M) : Submonoid.closure (s \ {1}) = Submonoid.closure s := Submonoid.closure_sdiff_eq_closure <| by simp [one_mem]

