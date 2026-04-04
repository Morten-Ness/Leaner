import Mathlib

variable {k E PE : Type*} [Field k] [AddCommGroup E] [Module k E] [AddTorsor E PE]

variable [LinearOrder k] [IsStrictOrderedRing k] [PartialOrder E] [IsOrderedAddMonoid E]
  [PosSMulMono k E] {f : k → E} {x y : k}

theorem StrictAntiOn.slope_neg {s : Set k} (hf : StrictAntiOn f s) (hx : x ∈ s) (hy : y ∈ s)
    (hxy : x ≠ y) : slope f x y < 0 := by
  simpa using hf.neg.slope_pos hx hy hxy

