import Mathlib

variable {G M R K : Type*}

variable [Field K] [LinearOrder K] [IsStrictOrderedRing K]

variable [Archimedean K] {x y ε : K}

theorem le_iff_forall_lt_rat_imp_le : x ≤ y ↔ ∀ q : ℚ, y < q → x ≤ q := ⟨fun hxy _ hqx ↦ hxy.trans hqx.le, le_of_forall_lt_rat_imp_le⟩

