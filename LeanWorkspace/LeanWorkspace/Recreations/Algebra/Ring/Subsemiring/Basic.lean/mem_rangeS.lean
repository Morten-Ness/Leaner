import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocSemiring R] (M : Submonoid R)

variable [NonAssocSemiring S] [NonAssocSemiring T]

variable (g : S →+* T) (f : R →+* S)

theorem mem_rangeS {f : R →+* S} {y : S} : y ∈ f.rangeS ↔ ∃ x, f x = y := Iff.rfl

