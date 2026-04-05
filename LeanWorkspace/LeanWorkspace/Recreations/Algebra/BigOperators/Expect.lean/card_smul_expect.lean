import Mathlib

open scoped Pointwise BigOperators

variable {ι κ M N : Type*}

variable [AddCommMonoid M] [Module ℚ≥0 M] [AddCommMonoid N] [Module ℚ≥0 N] {s t : Finset ι}
  {f g : ι → M} {p q : ι → Prop} [DecidablePred p] [DecidablePred q]

theorem card_smul_expect (s : Finset ι) (f : ι → M) : #s • 𝔼 i ∈ s, f i = ∑ i ∈ s, f i := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simp
  · rw [expect, ← Nat.cast_smul_eq_nsmul ℚ≥0, smul_inv_smul₀]
    exact mod_cast hs.card_ne_zero

