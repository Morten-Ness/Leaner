import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocSemiring R] (M : Submonoid R)

variable [NonAssocSemiring S] [NonAssocSemiring T]

set_option backward.isDefEq.respectTransparency false in
theorem mem_center_iff {R} [Semiring R] {z : R} : z ∈ Subsemiring.center R ↔ ∀ g, g * z = z * g := Subsemigroup.mem_center_iff

