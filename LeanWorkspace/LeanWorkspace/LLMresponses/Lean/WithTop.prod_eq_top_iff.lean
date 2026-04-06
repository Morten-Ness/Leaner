FAIL
import Mathlib

variable {ι M M₀ : Type*}

variable [CommMonoidWithZero M₀] [NoZeroDivisors M₀] [Nontrivial M₀] [DecidableEq M₀]
  {s : Finset ι} {f : ι → WithTop M₀} {i : ι}

theorem prod_eq_top_iff : ∏ j ∈ s, f j = ⊤ ↔ (∃ i ∈ s, f i = ⊤) ∧ (∀ i ∈ s, f i ≠ 0) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha]
      constructor
      · intro h
        have hne : f a ≠ 0 := by
          intro h0
          rw [h0, zero_mul] at h
          simp at h
        by_cases htop : f a = ⊤
        · refine ⟨⟨a, Finset.mem_insert_self a s, htop⟩, ?_⟩
          intro j hj
          rcases Finset.mem_insert.mp hj with rfl | hj'
          · exact hne
          · intro hj0
            have hs0 : ∏ x ∈ s, f x = 0 := by
              rw [Finset.prod_eq_zero_iff]
              exact ⟨j, hj', hj0⟩
            have : f a * ∏ x ∈ s, f x = 0 := by rw [hs0, mul_zero]
            rw [h] at this
            simp at this
        · have hs_top : ∏ x ∈ s, f x = ⊤ := by
            cases hfa : f a <;> simp [hfa] at h htop ⊢
          rcases ih.mp hs_top with ⟨⟨i, hi, hi_top⟩, hs_ne⟩
          refine ⟨⟨i, Finset.mem_insert_of_mem hi, hi_top⟩, ?_⟩
          intro j hj
          rcases Finset.mem_insert.mp hj with rfl | hj'
          · exact hne
          · exact hs_ne j hj'
      · rintro ⟨⟨i, hi, hi_top⟩, hne⟩
        rcases Finset.mem_insert.mp hi with rfl | hi'
        · rw [hi_top, top_mul]
          simp
        · have hs_top : ∏ x ∈ s, f x = ⊤ := by
            apply ih.mpr
            refine ⟨⟨i, hi', hi_top⟩, ?_⟩
            intro j hj
            exact hne j (Finset.mem_insert_of_mem hj)
          have hfa_ne : f a ≠ 0 := hne a (Finset.mem_insert_self a s)
          cases hfa : f a <;> simp [hfa] at hfa_ne hs_top ⊢
