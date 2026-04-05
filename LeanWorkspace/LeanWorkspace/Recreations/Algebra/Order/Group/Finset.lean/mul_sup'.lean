import Mathlib

open scoped Finset

variable {ι κ M G : Type*}

variable [Group G] [LinearOrder G]

set_option linter.docPrime false in
theorem mul_sup' [MulLeftMono G] (s : Finset ι) (f : ι → G) (a : G) (hs) :
    a * s.sup' hs f = s.sup' hs fun i ↦ a * f i := map_finset_sup' (OrderIso.mulLeft a) hs f

