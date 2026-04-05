import Mathlib

open scoped Pointwise BigOperators

variable {ι κ M N : Type*}

variable [Semifield M] [CharZero M] [Semifield N] [CharZero N] [Algebra M N]

theorem coe_expect (s : Finset ι) (f : ι → M) : 𝔼 i ∈ s, f i = 𝔼 i ∈ s, (f i : N) := map_expect (algebraMap _ _) _ _

