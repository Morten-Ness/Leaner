import Mathlib

open scoped Finset

variable {ι κ M G : Type*}

variable [Group G] [LinearOrder G]

theorem sup'_mul [MulRightMono G] (s : Finset ι) (f : ι → G) (a : G) (hs) :
    s.sup' hs f * a = s.sup' hs fun i ↦ f i * a := map_finset_sup' (OrderIso.mulRight a) hs f

