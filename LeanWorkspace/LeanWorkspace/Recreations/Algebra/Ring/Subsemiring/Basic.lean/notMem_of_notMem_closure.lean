import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocSemiring R] (M : Submonoid R)

variable [NonAssocSemiring S] [NonAssocSemiring T]

theorem notMem_of_notMem_closure {s : Set R} {P : R} (hP : P ∉ Subsemiring.closure s) : P ∉ s := fun h =>
  hP (Subsemiring.subset_closure h)

