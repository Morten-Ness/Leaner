import Mathlib

variable {ι M₀ G₀ : Type*}

theorem sup_div₀ [LinearOrderedCommGroupWithZero G₀] {a : G₀} (ha : 0 ≤ a)
    (s : Finset ι) (f : ι → G₀) : s.sup f / a = s.sup fun i ↦ f i / a := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simp [← show (0 : G₀) = ⊥ from bot_unique zero_le']
  rw [← Finset.sup'_eq_sup hs, ← Finset.sup'_eq_sup hs, Finset.sup'_div₀ (ha := ha)]

