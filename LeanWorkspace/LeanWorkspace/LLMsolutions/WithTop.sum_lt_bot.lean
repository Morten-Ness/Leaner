FAIL
import Mathlib

variable {ι M M₀ : Type*}

variable [AddCommMonoid M] {s : Finset ι} {f : ι → WithBot M}

variable [LT M]

theorem sum_lt_bot (h : ∀ i ∈ s, f i ≠ ⊥) : ⊥ < ∑ i ∈ s, f i := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert a s ha ih =>
      have ha' : f a ≠ ⊥ := h a (by simp)
      have hs : ∀ i ∈ s, f i ≠ ⊥ := by
        intro i hi
        exact h i (by simp [hi])
      have ih' : ⊥ < ∑ i ∈ s, f i := ih hs
      rw [Finset.sum_insert ha]
      cases hfa : f a with
      | bot =>
          exfalso
          exact ha' hfa
      | coe a' =>
          cases hsum : ∑ i ∈ s, f i with
          | bot =>
              simp at ih'
          | coe s' =>
              simp [hfa, hsum, WithBot.some_eq_coe]
