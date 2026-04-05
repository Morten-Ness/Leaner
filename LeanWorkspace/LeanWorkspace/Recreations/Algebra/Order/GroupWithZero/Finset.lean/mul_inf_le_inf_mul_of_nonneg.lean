import Mathlib

variable {ι M₀ G₀ : Type*}

variable [MonoidWithZero M₀] {s : Finset ι} {a b : ι → M₀}

theorem mul_inf_le_inf_mul_of_nonneg [SemilatticeInf M₀] [OrderTop M₀] [PosMulMono M₀] [MulPosMono M₀]
    (ha : ∀ i ∈ s, 0 ≤ a i) (hb : ∀ i ∈ s, 0 ≤ b i) : s.inf a * s.inf b ≤ s.inf (a * b) := Finset.le_inf fun i hi ↦ mul_le_mul (inf_le hi) (inf_le hi) (Finset.le_inf hb) (ha i hi)

