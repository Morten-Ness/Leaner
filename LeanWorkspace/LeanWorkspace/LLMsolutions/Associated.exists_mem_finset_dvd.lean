import Mathlib

variable {ι M M₀ : Type*}

variable [CommMonoidWithZero M₀] {p : M₀}

theorem exists_mem_finset_dvd (hp : Prime p) {s : Finset ι} {f : ι → M₀} :
    p ∣ s.prod f → ∃ i ∈ s, p ∣ f i := by
  classical
  induction s using Finset.induction with
  | empty =>
      intro h
      exfalso
      exact hp.not_dvd_one h
  | @insert a s ha ih =>
      intro h
      rw [Finset.prod_insert ha] at h
      rcases hp.2.2 _ _ h with h' | h'
      · exact ⟨a, Finset.mem_insert_self a s, h'⟩
      · rcases ih h' with ⟨i, hi, hpi⟩
        exact ⟨i, Finset.mem_insert_of_mem hi, hpi⟩
