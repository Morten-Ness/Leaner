import Mathlib

open scoped BigOperators Pointwise NNRat

variable {ι α R : Type*}

variable [AddCommMonoid α] [PartialOrder α] [IsOrderedAddMonoid α] [Module ℚ≥0 α]
  {s : Finset ι} {f g : ι → α}

variable {M N : Type*} [AddCommMonoid M] [Module ℚ≥0 M]
  [AddCommMonoid N] [PartialOrder N] [IsOrderedAddMonoid N] [Module ℚ≥0 N]
  [PosSMulMono ℚ≥0 N] {m : M → N} {p : M → Prop} {f : ι → M} {s : Finset ι}

theorem le_expect_of_subadditive (h_zero : m 0 = 0) (h_add : ∀ a b, m (a + b) ≤ m a + m b)
    (h_div : ∀ (n : ℕ) a, m (a /ℚ n) = m a /ℚ n) : m (𝔼 i ∈ s, f i) ≤ 𝔼 i ∈ s, m (f i) := Finset.le_expect_of_subadditive_on_pred (p := fun _ ↦ True) h_zero (by simpa) (by simp) (by simpa)
    (by simp)

