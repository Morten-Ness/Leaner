import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocRing R]

theorem mem_mk' {s : Set R} {sm : Submonoid R} (hm : ↑sm = s) {sa : AddSubgroup R} (ha : ↑sa = s)
    {x : R} : x ∈ Subring.mk' s sm sa hm ha ↔ x ∈ s := Iff.rfl

