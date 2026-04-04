import Mathlib

variable {k : Type*} {V1 : Type*} {P1 : Type*} {V2 : Type*} {P2 : Type*} {V3 : Type*}
  {P3 : Type*} {V4 : Type*} {P4 : Type*} [Ring k] [AddCommGroup V1] [Module k V1]
  [AddTorsor V1 P1] [AddCommGroup V2] [Module k V2] [AddTorsor V2 P2] [AddCommGroup V3]
  [Module k V3] [AddTorsor V3 P3] [AddCommGroup V4] [Module k V4] [AddTorsor V4 P4]

variable (k P1)

variable {k P1}

variable {P1}

variable {k}

variable (k) in

theorem lineMap_anti [LinearOrder k] [Preorder V1] [AddLeftMono V1] [SMulPosMono k V1]
    {p₀ p₁ : V1} (h : p₁ ≤ p₀) :
    Antitone (AffineMap.lineMap (k := k) p₀ p₁) := by
  intro x y hxy
  suffices y • (p₁ - p₀) ≤ x • (p₁ - p₀) by simpa [AffineMap.lineMap]
  rw [← neg_le_neg_iff, ← smul_neg, ← smul_neg]
  gcongr
  simpa

