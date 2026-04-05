import Mathlib

variable {ι α R S : Type*}

variable {S : Type*} [Semifield S] [LinearOrder S]

variable {R : Type*} [DivisionSemiring R] (abv : R → S) [IsAbsoluteValue abv]

theorem abv_div (a b : R) : abv (a / b) = abv a / abv b := map_div₀ (IsAbsoluteValue.abvHom' abv) a b

