import Mathlib

open scoped RightActions

variable {T : Type*} {S : Type*} {R : Type u} {M : Type v}

theorem inl_sum {ι} [AddCommMonoid R] [AddCommMonoid M] (s : Finset ι) (f : ι → R) :
    (TrivSqZeroExt.inl (∑ i ∈ s, f i) : tsze R M) = ∑ i ∈ s, TrivSqZeroExt.inl (f i) := map_sum (LinearMap.inl ℕ _ _) _ _

