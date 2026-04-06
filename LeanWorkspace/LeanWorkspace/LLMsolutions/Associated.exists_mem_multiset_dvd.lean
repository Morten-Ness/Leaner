FAIL
import Mathlib

variable {ι M M₀ : Type*}

variable [CommMonoidWithZero M₀] {p : M₀}

theorem exists_mem_multiset_dvd (hp : Prime p) {s : Multiset M₀} : p ∣ s.prod → ∃ a ∈ s, p ∣ a := by
  classical
  refine Quot.inductionOn s ?_
  intro l
  induction l with
  | nil =>
      intro h
      exfalso
      exact hp.not_dvd_one h
  | cons a t ih =>
      intro h
      simp only [Multiset.prod_cons] at h ⊢
      rcases hp.dvd_or_dvd h with ha | ht
      · exact ⟨a, Or.inl rfl, ha⟩
      · rcases ih ht with ⟨b, hb, hpb⟩
        exact ⟨b, Or.inr hb, hpb⟩
