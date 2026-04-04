import Mathlib

variable {k E PE : Type*} [Field k] [AddCommGroup E] [Module k E] [AddTorsor E PE]

variable [LinearOrder k] [IsStrictOrderedRing k] [PartialOrder E] [IsOrderedAddMonoid E]
  [PosSMulMono k E] {f : k → E} {x y : k}

theorem AntitoneOn.slope_nonpos {s : Set k} (hf : AntitoneOn f s) (hx : x ∈ s) (hy : y ∈ s) :
    slope f x y ≤ 0 := by
  simpa using hf.neg.slope_nonneg hx hy

