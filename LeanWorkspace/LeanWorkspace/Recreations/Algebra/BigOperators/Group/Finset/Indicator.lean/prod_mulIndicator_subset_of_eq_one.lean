import Mathlib

variable {ι κ α β : Type*} [CommMonoid β]

theorem prod_mulIndicator_subset_of_eq_one [One α] (f : ι → α) (g : ι → α → β) {s t : Finset ι}
    (h : s ⊆ t) (hg : ∀ a, g a 1 = 1) :
    ∏ i ∈ t, g i (mulIndicator ↑s f i) = ∏ i ∈ s, g i (f i) := by
  calc
    _ = ∏ i ∈ s, g i (mulIndicator ↑s f i) := by rw [prod_subset h fun i _ hn ↦ by simp [hn, hg]]
    _ = _ := prod_congr rfl fun i hi ↦ congr_arg _ <| mulIndicator_of_mem hi f

