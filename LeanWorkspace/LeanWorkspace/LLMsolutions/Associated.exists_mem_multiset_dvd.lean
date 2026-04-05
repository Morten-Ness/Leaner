import Mathlib

variable {ι M M₀ : Type*}

variable [CommMonoidWithZero M₀] {p : M₀}

theorem exists_mem_multiset_dvd (hp : Prime p) {s : Multiset M₀} : p ∣ s.prod → ∃ a ∈ s, p ∣ a := by
  classical
  refine Multiset.induction_on s ?_ ?_
  · intro h
    exfalso
    exact hp.not_dvd_one h
  · intro a s ih h
    rw [Multiset.prod_cons] at h
    rcases hp.dvd_or_dvd h with ha | hs
    · exact ⟨a, by simp, ha⟩
    · rcases ih hs with ⟨b, hb, hpb⟩
      exact ⟨b, by simp [hb], hpb⟩
