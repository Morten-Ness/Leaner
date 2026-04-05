import Mathlib

variable {G M N : Type*} {α β ι : Sort*} [CommMonoid M] [CommMonoid N]

theorem finprod_one : (∏ᶠ _ : α, (1 : M)) = 1 := by
  have : (mulSupport fun x : PLift α => (fun _ => 1 : α → M) x.down) ⊆ (∅ : Finset (PLift α)) :=
    fun x h => by simp at h
  rw [finprod_eq_prod_plift_of_mulSupport_subset this, Finset.prod_empty]

