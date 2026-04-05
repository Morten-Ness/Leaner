import Mathlib

variable {ι M₀ G₀ : Type*}

variable [MonoidWithZero M₀] {s : Finset ι} {a b : ι → M₀}

theorem inf'_mul_le_mul_inf'_of_nonneg [SemilatticeInf M₀] [PosMulMono M₀] [MulPosMono M₀]
    (ha : ∀ i ∈ s, 0 ≤ a i) (hb : ∀ i ∈ s, 0 ≤ b i) (hs) :
    s.inf' hs a * s.inf' hs b ≤ s.inf' hs (a * b) := le_inf' _ _ fun _i hi ↦ mul_le_mul (inf'_le _ hi) (inf'_le _ hi) (le_inf' _ _ hb) (ha _ hi)

