import Mathlib

variable {ι M₀ G₀ : Type*}

variable [MonoidWithZero M₀] {s : Finset ι} {a b : ι → M₀}

theorem sup'_mul_le_mul_sup'_of_nonneg [SemilatticeSup M₀] [PosMulMono M₀] [MulPosMono M₀]
    (ha : ∀ i ∈ s, 0 ≤ a i) (hb : ∀ i ∈ s, 0 ≤ b i) (hs) :
    s.sup' hs (a * b) ≤ s.sup' hs a * s.sup' hs b := sup'_le _ _ fun _i hi ↦
    mul_le_mul (le_sup' _ hi) (le_sup' _ hi) (hb _ hi) ((ha _ hi).trans <| le_sup' _ hi)

