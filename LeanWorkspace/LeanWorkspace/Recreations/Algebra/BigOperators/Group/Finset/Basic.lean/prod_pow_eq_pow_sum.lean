import Mathlib

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable [CommMonoid M] {f g : ι → M}

theorem prod_pow_eq_pow_sum (s : Finset ι) (f : ι → ℕ) (a : M) :
    ∏ i ∈ s, a ^ f i = a ^ ∑ i ∈ s, f i := cons_induction (by simp) (fun _ _ _ _ ↦ by simp [Finset.prod_cons, sum_cons, pow_add, *]) s

