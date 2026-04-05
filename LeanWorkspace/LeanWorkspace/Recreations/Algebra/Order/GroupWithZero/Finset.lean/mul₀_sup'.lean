import Mathlib

variable {ι M₀ G₀ : Type*}

variable [GroupWithZero G₀] [SemilatticeSup G₀] {s : Finset ι} {a : G₀}

set_option linter.docPrime false in
theorem mul₀_sup' [PosMulReflectLT G₀] (ha : 0 ≤ a) (f : ι → G₀) (s : Finset ι) (hs) :
    a * s.sup' hs f = s.sup' hs fun i ↦ a * f i := by
  by_cases! h : 0 = a
  · simp [← h]
  exact map_finset_sup' (OrderIso.mulLeft₀ _ (lt_of_le_of_ne ha h)) hs f

