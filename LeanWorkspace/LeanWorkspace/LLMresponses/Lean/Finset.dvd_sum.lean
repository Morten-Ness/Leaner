import Mathlib

variable {ι κ M R : Type*} {s s₁ s₂ : Finset ι} {i : ι}

variable [NonUnitalSemiring R] {f : ι → R} {a : R}

theorem dvd_sum (h : ∀ i ∈ s, a ∣ f i) : a ∣ ∑ i ∈ s, f i := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert b s hb ih =>
      have hb' : a ∣ f b := h b (Finset.mem_insert_self b s)
      have hs' : ∀ i ∈ s, a ∣ f i := by
        intro i hi
        exact h i (Finset.mem_insert_of_mem hi)
      simpa [Finset.sum_insert hb] using dvd_add hb' (ih hs')
