import Mathlib

theorem MulEquiv.strictMono_symm {G G' : Type*} [CommMonoid G] [LinearOrder G]
    [CommMonoid G'] [Preorder G'] {e : G ≃* G'} (he : StrictMono e) : StrictMono e.symm := by
  intro
  simp [← he.lt_iff_lt]

