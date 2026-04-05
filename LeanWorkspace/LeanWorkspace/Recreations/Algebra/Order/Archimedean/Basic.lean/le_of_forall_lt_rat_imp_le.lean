import Mathlib

variable {G M R K : Type*}

variable [Field K] [LinearOrder K] [IsStrictOrderedRing K]

variable [Archimedean K] {x y ε : K}

theorem le_of_forall_lt_rat_imp_le (h : ∀ q : ℚ, y < q → x ≤ q) : x ≤ y := le_of_not_gt fun hyx =>
    let ⟨_, hy, hx⟩ := exists_rat_btwn hyx
    hx.not_ge <| h _ hy

