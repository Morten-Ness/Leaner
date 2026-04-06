import Mathlib

variable {ι M M₀ : Type*}

variable [CommMonoidWithZero M₀] {p : M₀}

theorem exists_mem_finset_dvd (hp : Prime p) {s : Finset ι} {f : ι → M₀} :
    p ∣ s.prod f → ∃ i ∈ s, p ∣ f i := by
  classical
  refine Finset.induction_on s ?_ ?_
  · intro h
    exfalso
    exact hp.not_dvd_one h
  · intro a s ha ih hdiv
    rw [Finset.prod_insert ha] at hdiv
    rcases hp.dvd_or_dvd hdiv with hpa | hps
    · exact ⟨a, Finset.mem_insert_self a s, hpa⟩
    · rcases ih hps with ⟨i, his, hpi⟩
      exact ⟨i, Finset.mem_insert_of_mem his, hpi⟩
