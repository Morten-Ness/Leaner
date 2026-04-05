import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocSemiring R] (M : Submonoid R)

variable [NonAssocSemiring S] [NonAssocSemiring T]

theorem top_prod_top : (⊤ : Subsemiring R).prod (⊤ : Subsemiring S) = ⊤ := (Subsemiring.top_prod _).trans <| Subsemiring.comap_top _

