import Mathlib

variable {M : Type*} {N : Type*}

variable [MulOneClass M] {s : Set M}

variable [MulOneClass N]

theorem mem_eqLocusM {f g : M →* N} {x : M} : x ∈ f.eqLocusM g ↔ f x = g x := Iff.rfl

