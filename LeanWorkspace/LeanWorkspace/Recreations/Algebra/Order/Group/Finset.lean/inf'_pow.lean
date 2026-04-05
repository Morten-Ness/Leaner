import Mathlib

open scoped Finset

variable {ι κ M G : Type*}

theorem inf'_pow [LinearOrder M] [Monoid M] [MulLeftMono M] [MulRightMono M] (s : Finset ι)
    (f : ι → M) (n : ℕ) (hs) : s.inf' hs f ^ n = s.inf' hs fun a ↦ f a ^ n := map_finset_inf' (OrderHom.mk _ <| pow_left_mono n) hs _

