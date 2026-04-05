import Mathlib

variable {ι M₀ G₀ : Type*}

variable [GroupWithZero G₀] [SemilatticeSup G₀] {s : Finset ι} {a : G₀}

theorem sup'_mul₀ [MulPosReflectLT G₀] (ha : 0 ≤ a) (f : ι → G₀) (s : Finset ι) (hs) :
    s.sup' hs f * a = s.sup' hs fun i ↦ f i * a := by
  by_cases! h : 0 = a
  · simp [← h]
  exact map_finset_sup' (OrderIso.mulRight₀ _ (lt_of_le_of_ne ha h)) hs f

