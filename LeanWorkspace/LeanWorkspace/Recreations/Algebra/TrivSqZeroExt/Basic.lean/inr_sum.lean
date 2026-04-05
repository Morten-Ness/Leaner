import Mathlib

open scoped RightActions

variable {T : Type*} {S : Type*} {R : Type u} {M : Type v}

theorem inr_sum {ι} [AddCommMonoid R] [AddCommMonoid M] (s : Finset ι) (f : ι → M) :
    (TrivSqZeroExt.inr (∑ i ∈ s, f i) : tsze R M) = ∑ i ∈ s, TrivSqZeroExt.inr (f i) := map_sum (LinearMap.inr ℕ _ _) _ _

