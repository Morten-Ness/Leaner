import Mathlib

variable {ι M M₀ : Type*}

theorem exists_associated_mem_of_dvd_prod [CommMonoidWithZero M₀] [IsCancelMulZero M₀]
    {p : M₀} (hp : Prime p)
    {s : Multiset M₀} : (∀ r ∈ s, Prime r) → p ∣ s.prod → ∃ q ∈ s, p ~ᵤ q := Multiset.induction_on s (by simp [mt isUnit_iff_dvd_one.2 hp.not_unit]) fun a s ih hs hps => by
    rw [Multiset.prod_cons] at hps
    rcases hp.dvd_or_dvd hps with h | h
    · have hap := hs a (Multiset.mem_cons.2 (Or.inl rfl))
      exact ⟨a, Multiset.mem_cons_self a _, hp.associated_of_dvd hap h⟩
    · rcases ih (fun r hr => hs _ (Multiset.mem_cons.2 (Or.inr hr))) h with ⟨q, hq₁, hq₂⟩
      exact ⟨q, Multiset.mem_cons.2 (Or.inr hq₁), hq₂⟩

