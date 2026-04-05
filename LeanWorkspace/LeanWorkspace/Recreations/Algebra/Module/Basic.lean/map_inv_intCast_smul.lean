import Mathlib

variable {α R M M₂ : Type*}

theorem map_inv_intCast_smul [AddCommGroup M] [AddCommGroup M₂] {F : Type*} [FunLike F M M₂]
    [AddMonoidHomClass F M M₂] (f : F) (R S : Type*) [DivisionRing R] [DivisionRing S] [Module R M]
    [Module S M₂] (z : ℤ) (x : M) : f ((z⁻¹ : R) • x) = (z⁻¹ : S) • f x := by
  obtain ⟨n, rfl | rfl⟩ := z.eq_nat_or_neg
  · rw [Int.cast_natCast, Int.cast_natCast, map_inv_natCast_smul _ R S]
  · simp_rw [Int.cast_neg, Int.cast_natCast, inv_neg, neg_smul, map_neg,
      map_inv_natCast_smul _ R S]

