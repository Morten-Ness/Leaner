import Mathlib

variable {G M R K : Type*}

variable [Field K] [LinearOrder K] [IsStrictOrderedRing K]

variable [Archimedean K] {x y ε : K}

theorem le_of_forall_rat_lt_imp_le (h : ∀ q : ℚ, (q : K) < x → (q : K) ≤ y) : x ≤ y := le_of_not_gt fun hyx =>
    let ⟨_, hy, hx⟩ := exists_rat_btwn hyx
    hy.not_ge <| h _ hx

