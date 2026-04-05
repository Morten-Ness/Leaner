import Mathlib

variable {M : Type*} [Monoid M]

theorem mem_ofUnits_iff (S : Subgroup Mˣ) (x : M) : x ∈ S.ofUnits ↔ ∃ y ∈ S, y = x := Iff.rfl

