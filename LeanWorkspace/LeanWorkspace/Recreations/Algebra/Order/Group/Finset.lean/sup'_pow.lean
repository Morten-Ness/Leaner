import Mathlib

open scoped Finset

variable {ι κ M G : Type*}

theorem sup'_pow [LinearOrder M] [Monoid M] [MulLeftMono M] [MulRightMono M] (s : Finset ι)
    (f : ι → M) (n : ℕ) (hs) : s.sup' hs f ^ n = s.sup' hs fun a ↦ f a ^ n := map_finset_sup' (OrderHom.mk _ <| pow_left_mono n) hs _

