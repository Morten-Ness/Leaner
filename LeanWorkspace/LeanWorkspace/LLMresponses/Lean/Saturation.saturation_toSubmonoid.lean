FAIL
import Mathlib

variable {M : Type*}

variable [MulOneClass M]

variable {a : Submonoid M} {b : SaturatedSubmonoid M}

theorem saturation_toSubmonoid : b.saturation = b := by
  ext x
  exact Iff.intro (fun hx => hx.2 b (le_rfl : b.toSubmonoid ≤ b.toSubmonoid)) fun hx =>
    by
      refine ⟨?_, ?_⟩
      · simpa using b.one_mem
      · intro t ht
        exact ht hx
