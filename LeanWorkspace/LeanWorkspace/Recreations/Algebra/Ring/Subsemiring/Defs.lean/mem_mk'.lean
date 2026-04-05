import Mathlib

variable {R : Type u} {S : Type v} [NonAssocSemiring R]

variable [NonAssocSemiring S]

theorem mem_mk' {s : Set R} {sm : Submonoid R} (hm : ↑sm = s) {sa : AddSubmonoid R} (ha : ↑sa = s)
    {x : R} : x ∈ Subsemiring.mk' s sm hm sa ha ↔ x ∈ s := Iff.rfl

