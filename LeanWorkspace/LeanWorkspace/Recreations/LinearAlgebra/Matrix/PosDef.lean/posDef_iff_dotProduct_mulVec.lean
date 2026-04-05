import Mathlib

variable {m n R R' : Type*}

variable [Ring R] [PartialOrder R] [StarRing R]

variable [CommRing R'] [PartialOrder R'] [StarRing R']

variable [Fintype n] [Fintype m]

theorem posDef_iff_dotProduct_mulVec {M : Matrix n n R} :
    M.PosDef ↔ M.IsHermitian ∧ ∀ ⦃x⦄, x ≠ 0 → 0 < star x ⬝ᵥ (M *ᵥ x) := by
  have (x : n →₀ R) : x = 0 ↔ Finsupp.equivFunOnFinite x = 0 :=
    ⟨fun h1 ↦ Finsupp.coe_eq_zero.mpr h1,fun h2 ↦ Finsupp.coe_eq_zero.mp h2⟩
  simp [Matrix.PosDef, ← Finsupp.equivFunOnFinite.forall_congr_right, dotProduct, mulVec,
    Finsupp.sum_fintype, Finset.mul_sum, mul_assoc, this]

