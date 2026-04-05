import Mathlib

variable {α R S : Type*} {n : ℕ}

variable [NonAssocSemiring R] [NonAssocSemiring S]

theorem charZero (ϕ : R →+* S) [CharZero S] : CharZero R where
  cast_injective a b h := CharZero.cast_injective (R := S) <| by
    rw [← map_natCast ϕ, ← map_natCast ϕ, h]

