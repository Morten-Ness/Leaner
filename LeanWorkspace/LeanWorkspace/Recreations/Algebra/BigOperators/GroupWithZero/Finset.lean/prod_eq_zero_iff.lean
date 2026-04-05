import Mathlib

variable {ι κ G₀ M₀ : Type*} {α : ι → Type*}

variable [CommMonoidWithZero M₀] {p : ι → Prop} [DecidablePred p] {f : ι → M₀} {s : Finset ι}
  {i : ι}

variable [Nontrivial M₀] [NoZeroDivisors M₀]

theorem prod_eq_zero_iff : ∏ x ∈ s, f x = 0 ↔ ∃ a ∈ s, f a = 0 := by
  classical
    induction s using Finset.induction_on with
    | empty => exact ⟨Not.elim one_ne_zero, fun ⟨_, H, _⟩ => by simp at H⟩
    | insert _ _ ha ih => rw [prod_insert ha, mul_eq_zero, exists_mem_insert, ih]

