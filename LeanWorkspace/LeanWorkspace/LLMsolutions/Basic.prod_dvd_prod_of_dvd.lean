import Mathlib

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable [CommMonoid M] {f g : ι → M}

theorem prod_dvd_prod_of_dvd (f g : ι → M) (h : ∀ i ∈ s, f i ∣ g i) :
    ∏ i ∈ s, f i ∣ ∏ i ∈ s, g i := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert a s ha ih =>
      have h₁ : f a ∣ g a := h a (Finset.mem_insert_self a s)
      have h₂ : ∀ i ∈ s, f i ∣ g i := by
        intro i hi
        exact h i (Finset.mem_insert_of_mem hi)
      rcases h₁ with ⟨c, hc⟩
      rcases ih h₂ with ⟨d, hd⟩
      refine ⟨c * d, ?_⟩
      rw [Finset.prod_insert ha, Finset.prod_insert ha, hc, hd]
      ac_rfl
