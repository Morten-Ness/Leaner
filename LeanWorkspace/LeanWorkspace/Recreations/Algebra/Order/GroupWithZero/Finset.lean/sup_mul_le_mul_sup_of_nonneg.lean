import Mathlib

variable {ι M₀ G₀ : Type*}

variable [MonoidWithZero M₀] {s : Finset ι} {a b : ι → M₀}

theorem sup_mul_le_mul_sup_of_nonneg [SemilatticeSup M₀] [OrderBot M₀] [PosMulMono M₀] [MulPosMono M₀]
    (ha : ∀ i ∈ s, 0 ≤ a i) (hb : ∀ i ∈ s, 0 ≤ b i) : s.sup (a * b) ≤ s.sup a * s.sup b := Finset.sup_le fun _i hi ↦
    mul_le_mul (le_sup hi) (le_sup hi) (hb _ hi) ((ha _ hi).trans <| le_sup hi)

