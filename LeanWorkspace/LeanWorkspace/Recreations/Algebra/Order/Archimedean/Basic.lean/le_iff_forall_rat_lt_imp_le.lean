import Mathlib

variable {G M R K : Type*}

variable [Field K] [LinearOrder K] [IsStrictOrderedRing K]

variable [Archimedean K] {x y ε : K}

theorem le_iff_forall_rat_lt_imp_le : x ≤ y ↔ ∀ q : ℚ, (q : K) < x → (q : K) ≤ y := ⟨fun hxy _ hqx ↦ hqx.le.trans hxy, le_of_forall_rat_lt_imp_le⟩

