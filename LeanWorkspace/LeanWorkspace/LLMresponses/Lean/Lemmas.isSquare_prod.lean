import Mathlib

variable {ι κ M N β : Type*}

variable [CommMonoid M]

theorem isSquare_prod {s : Finset ι} (f : ι → M) (h : ∀ c ∈ s, IsSquare (f c)) :
    IsSquare (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      exact ⟨1, by simp⟩
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha]
      rcases h a (Finset.mem_insert_self a s) with ⟨x, hx⟩
      rcases ih (by
        intro c hc
        exact h c (Finset.mem_insert_of_mem hc)) with ⟨y, hy⟩
      refine ⟨x * y, ?_⟩
      rw [hx, hy]
      simp [mul_left_comm, mul_comm]
