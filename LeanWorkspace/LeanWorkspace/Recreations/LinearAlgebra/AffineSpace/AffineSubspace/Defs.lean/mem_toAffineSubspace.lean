import Mathlib

variable {k V : Type*} [Ring k] [AddCommGroup V] [Module k V]

theorem mem_toAffineSubspace {p : Submodule k V} {x : V} :
    x ∈ p.toAffineSubspace ↔ x ∈ p := Iff.rfl

