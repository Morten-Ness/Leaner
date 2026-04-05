import Mathlib

variable {m n R R' : Type*}

variable [Ring R] [PartialOrder R] [StarRing R]

variable [CommRing R'] [PartialOrder R'] [StarRing R']

variable [Fintype n] [Fintype m]

variable [StarOrderedRing R']

omit [Fintype n] in variable [Finite n] in
theorem fromBlocks₁₁ [DecidableEq m] {A : Matrix m m R'}
    (B : Matrix m n R') (D : Matrix n n R') (hA : A.PosDef) [Invertible A] :
    (fromBlocks A B Bᴴ D).PosSemidef ↔ (D - Bᴴ * A⁻¹ * B).PosSemidef := by
  have := Fintype.ofFinite n
  rw [Matrix.posSemidef_iff_dotProduct_mulVec, IsHermitian.fromBlocks₁₁ _ _ hA.1]
  constructor
  · refine fun h => .of_dotProduct_mulVec_nonneg h.1 fun x => ?_
    have := h.2 (-((A⁻¹ * B) *ᵥ x) ⊕ᵥ x)
    rwa [dotProduct_mulVec, schur_complement_eq₁₁ B D _ _ hA.1, neg_add_cancel, dotProduct_zero,
      zero_add, ← dotProduct_mulVec] at this
  · refine fun h => ⟨h.1, fun x => ?_⟩
    rw [dotProduct_mulVec, ← Sum.elim_comp_inl_inr x, schur_complement_eq₁₁ B D _ _ hA.1]
    apply le_add_of_nonneg_of_le
    · rw [← dotProduct_mulVec]
      apply (Matrix.posSemidef_iff_dotProduct_mulVec.mp Matrix.PosDef.posSemidef hA).2
    · rw [← dotProduct_mulVec (star (x ∘ Sum.inr))]
      apply (Matrix.posSemidef_iff_dotProduct_mulVec.mp h).2

