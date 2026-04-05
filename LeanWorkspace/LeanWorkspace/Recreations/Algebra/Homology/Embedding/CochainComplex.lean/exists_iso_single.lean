import Mathlib

variable {C : Type*} [Category* C]

variable [HasZeroMorphisms C] (K L : CochainComplex C ℤ) (φ : K ⟶ L) (e : K ≅ L)

variable [HasZeroObject C]

theorem exists_iso_single (n : ℤ) [K.IsStrictlyGE n] [K.IsStrictlyLE n] :
    ∃ (M : C), Nonempty (K ≅ (single _ _ n).obj M) := ⟨K.X n, ⟨{
      hom := mkHomToSingle (𝟙 _) (fun i (hi : i + 1 = n) ↦
        (K.isZero_of_isStrictlyGE n i (by lia)).eq_of_src _ _)
      inv := mkHomFromSingle (𝟙 _) (fun i (hi : n + 1 = i) ↦
        (K.isZero_of_isStrictlyLE n i (by lia)).eq_of_tgt _ _)
      hom_inv_id := by
        ext i
        obtain hi | rfl | hi := lt_trichotomy i n
        · apply (K.isZero_of_isStrictlyGE n i (by lia)).eq_of_src
        · simp
        · apply (K.isZero_of_isStrictlyLE n i (by lia)).eq_of_tgt
      inv_hom_id := by aesop }⟩⟩

