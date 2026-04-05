import Mathlib

open scoped Pointwise BigOperators

variable {ι κ M N : Type*}

variable [AddCommMonoid M] [Module ℚ≥0 M] [AddCommMonoid N] [Module ℚ≥0 N] {s t : Finset ι}
  {f g : ι → M} {p q : ι → Prop} [DecidablePred p] [DecidablePred q]

theorem expectWith_congr (hst : s = t) (hpq : ∀ i ∈ t, p i ↔ q i) (h : ∀ i ∈ t, q i → f i = g i) :
    𝔼 i ∈ s with p i, f i = 𝔼 i ∈ t with q i, g i := Finset.expect_congr (by rw [hst, filter_inj'.2 hpq]) <| by simpa using h

