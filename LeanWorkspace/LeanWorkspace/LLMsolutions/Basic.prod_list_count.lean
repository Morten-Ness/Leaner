FAIL
import Mathlib

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable [CommMonoid M] {f g : ι → M}

theorem prod_list_count [DecidableEq M] (s : List M) :
    s.prod = ∏ m ∈ s.toFinset, m ^ s.count m := by
  classical
  induction s with
  | nil =>
      simp
  | cons a s ih =>
      by_cases ha : a ∈ s
      · rw [List.toFinset_cons_of_mem ha]
        rw [List.prod_cons, ih]
        refine Finset.prod_congr rfl ?_
        intro x hx
        by_cases hax : x = a
        · subst hax
          simp [List.count_cons, ha, pow_succ]
        · simp [List.count_cons, hax]
      · rw [List.toFinset_cons_of_not_mem ha]
        rw [List.prod_cons, ih]
        rw [Finset.prod_insert]
        · simp [List.count_cons, ha, pow_succ]
        · simpa using ha
