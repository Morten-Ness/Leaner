import Mathlib

variable {M : Type*} {N : Type*}

variable {A : Type*}

variable [MulOneClass M] {s : Set M}

variable [AddZeroClass A] {t : Set A}

variable (S : Submonoid M)

theorem closure_eq : Submonoid.closure (S : Set M) = S := (Submonoid.gi M).l_u_eq S

