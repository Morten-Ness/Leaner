import Mathlib

variable {ι κ M β γ : Type*} {s : Finset ι}

variable [CommMonoid M]

theorem prod_ite_one (s : Finset ι) (p : ι → Prop) [DecidablePred p]
    (h : ∀ i ∈ s, ∀ j ∈ s, p i → p j → i = j) (a : M) :
    ∏ i ∈ s, ite (p i) a 1 = ite (∃ i ∈ s, p i) a 1 := by
  split_ifs with h
  · obtain ⟨i, hi, hpi⟩ := h
    rw [prod_eq_single_of_mem _ hi, if_pos hpi]
    exact fun j hj hji ↦ if_neg fun hpj ↦ hji <| h _ hj _ hi hpj hpi
  · push Not at h
    rw [prod_eq_one]
    exact fun i hi => if_neg (h i hi)

