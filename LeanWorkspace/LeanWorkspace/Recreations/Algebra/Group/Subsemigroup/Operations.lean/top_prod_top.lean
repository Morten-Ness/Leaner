import Mathlib

variable {M N P σ : Type*}

variable [Mul M] [Mul N] [Mul P] (S : Subsemigroup M)

theorem top_prod_top : (⊤ : Subsemigroup M).prod (⊤ : Subsemigroup N) = ⊤ := (Subsemigroup.top_prod _).trans <| Subsemigroup.comap_top _

