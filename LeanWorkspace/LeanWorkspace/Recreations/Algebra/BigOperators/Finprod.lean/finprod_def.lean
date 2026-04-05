import Mathlib

variable {α β ι G M N : Type*} [CommMonoid M] [CommMonoid N]

theorem finprod_def (f : α → M) [Decidable (HasFiniteMulSupport f)] :
    ∏ᶠ i : α, f i = if h : HasFiniteMulSupport f then ∏ i ∈ h.toFinset, f i else 1 := by
  split_ifs with h
  · exact finprod_eq_prod_of_mulSupport_toFinset_subset _ h (Finset.Subset.refl _)
  · rw [finprod, dif_neg]
    rw [HasFiniteMulSupport, mulSupport_comp_eq_preimage]
    exact mt (fun hf => hf.of_preimage Equiv.plift.surjective) h

