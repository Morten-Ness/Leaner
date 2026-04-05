import Mathlib

variable {ι κ G₀ M₀ : Type*} {α : ι → Type*}

variable [CommMonoidWithZero M₀] {p : ι → Prop} [DecidablePred p] {f : ι → M₀} {s : Finset ι}
  {i : ι}

theorem prod_ite_zero :
    (∏ i ∈ s, if p i then f i else 0) = if ∀ i ∈ s, p i then ∏ i ∈ s, f i else 0 := by
  split_ifs with h
  · exact prod_congr rfl fun i hi => by simp [h i hi]
  · push Not at h
    rcases h with ⟨i, hi, hq⟩
    exact Finset.prod_eq_zero hi (by simp [hq])

