import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocSemiring R] (M : Submonoid R)

variable [NonAssocSemiring S] [NonAssocSemiring T]

theorem centralizer_centralizer_centralizer {R} [Semiring R] {s : Set R} :
    Subsemiring.centralizer s.centralizer.centralizer = Subsemiring.centralizer s := by
  apply SetLike.coe_injective
  simp only [Subsemiring.coe_centralizer, Set.centralizer_centralizer_centralizer]

