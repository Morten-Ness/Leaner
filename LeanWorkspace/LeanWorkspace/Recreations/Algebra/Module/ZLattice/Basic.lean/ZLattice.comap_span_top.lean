import Mathlib

variable (K : Type*) [NormedField K] {E F : Type*} [NormedAddCommGroup E] [NormedSpace K E]
    [NormedAddCommGroup F] [NormedSpace K F] (L : Submodule ℤ E)

theorem ZLattice.comap_span_top (hL : span K (L : Set E) = ⊤) {e : F →ₗ[K] E}
    (he : (L : Set E) ⊆ LinearMap.range e) :
    span K (ZLattice.comap K L e : Set F) = ⊤ := by
  rw [ZLattice.coe_comap, Submodule.span_preimage_eq (Submodule.nonempty L) he, hL, comap_top]

