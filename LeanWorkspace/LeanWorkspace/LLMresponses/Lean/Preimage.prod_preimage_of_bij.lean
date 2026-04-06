FAIL
import Mathlib

variable {ι κ β : Type*}

variable [CommMonoid β]

theorem prod_preimage_of_bij (f : ι → κ) (s : Finset κ) (hf : Set.BijOn f (f ⁻¹' ↑s) ↑s) (g : κ → β) :
    ∏ x ∈ s.preimage f hf.injOn, g (f x) = ∏ x ∈ s, g x := by
  classical
  rw [← Finset.prod_attach s]
  refine Finset.prod_bij' (fun x hx => ⟨f x, ?_⟩) ?_ ?_ ?_
  · exact hf.mapsTo hx
  · intro x hx
    simp
  · intro y hy
    rcases hf.surjOn hy with ⟨x, hx, rfl⟩
    refine ⟨x, hx, ?_⟩
    simp
  · intro x hx
    simp
