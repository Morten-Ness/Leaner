import Mathlib

variable (R : Type u) (L : Type v) (M : Type w)

variable [CommRing R] [LieRing L] [AddCommGroup M] [Module R M]

variable [LieRingModule L M]

variable [LieAlgebra R L]

variable (K : LieSubalgebra R L)

theorem exists_nested_lieIdeal_coe_eq_iff {K' : LieSubalgebra R L} (h : K ≤ K') :
    (∃ I : LieIdeal R K', ↑I = ofLe h) ↔ ∀ x y : L, x ∈ K' → y ∈ K → ⁅x, y⁆ ∈ K := by
  simp only [LieSubalgebra.exists_lieIdeal_coe_eq_iff, coe_bracket, mem_ofLe]
  constructor
  · intro h' x y hx hy; exact h' ⟨x, hx⟩ ⟨y, h hy⟩ hy
  · rintro h' ⟨x, hx⟩ ⟨y, hy⟩ hy'; exact h' x y hx hy'

