import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocSemiring R] (M : Submonoid R)

variable [NonAssocSemiring S] [NonAssocSemiring T]

theorem mem_centralizer_iff {R} [Semiring R] {s : Set R} {z : R} :
    z ∈ Subsemiring.centralizer s ↔ ∀ g ∈ s, g * z = z * g := Iff.rfl

