import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocSemiring R] (M : Submonoid R)

variable [NonAssocSemiring S] [NonAssocSemiring T]

theorem mem_closure {x : R} {s : Set R} : x ∈ Subsemiring.closure s ↔ ∀ S : Subsemiring R, s ⊆ S → x ∈ S := Subsemiring.mem_sInf

