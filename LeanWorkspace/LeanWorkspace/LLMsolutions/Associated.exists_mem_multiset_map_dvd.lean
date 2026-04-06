import Mathlib

variable {ι M M₀ : Type*}

variable [CommMonoidWithZero M₀] {p : M₀}

theorem exists_mem_multiset_map_dvd (hp : Prime p) {s : Multiset ι} {f : ι → M₀} :
    p ∣ (s.map f).prod → ∃ a ∈ s, p ∣ f a := by
  classical
  induction s using Multiset.induction_on with
  | empty =>
      intro h
      exfalso
      exact hp.not_dvd_one h
  | @cons a s ih =>
      intro h
      simp only [Multiset.map_cons, Multiset.prod_cons] at h
      rcases hp.dvd_or_dvd h with hpa | hps
      · exact ⟨a, by simp, hpa⟩
      · rcases ih hps with ⟨b, hb, hpb⟩
        exact ⟨b, by simp [hb], hpb⟩
