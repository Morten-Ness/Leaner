import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocSemiring R] (M : Submonoid R)

variable [NonAssocSemiring S] [NonAssocSemiring T]

theorem mem_closure_of_mem {s : Set R} {x : R} (hx : x ∈ s) : x ∈ Subsemiring.closure s := Subsemiring.subset_closure hx

