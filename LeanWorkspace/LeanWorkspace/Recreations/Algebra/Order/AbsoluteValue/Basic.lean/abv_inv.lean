import Mathlib

variable {ι α R S : Type*}

variable {S : Type*} [Semifield S] [LinearOrder S]

variable {R : Type*} [DivisionSemiring R] (abv : R → S) [IsAbsoluteValue abv]

theorem abv_inv (a : R) : abv a⁻¹ = (abv a)⁻¹ := map_inv₀ (IsAbsoluteValue.abvHom' abv) a

