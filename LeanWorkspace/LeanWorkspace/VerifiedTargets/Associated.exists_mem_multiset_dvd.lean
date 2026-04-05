import Mathlib

variable {ι M M₀ : Type*}

variable [CommMonoidWithZero M₀] {p : M₀}

theorem exists_mem_multiset_dvd (hp : Prime p) {s : Multiset M₀} : p ∣ s.prod → ∃ a ∈ s, p ∣ a := Multiset.induction_on s (fun h => (hp.not_dvd_one h).elim) fun a s ih h =>
    have : p ∣ a * s.prod := by simpa using h
    match hp.dvd_or_dvd this with
    | Or.inl h => ⟨a, Multiset.mem_cons_self a s, h⟩
    | Or.inr h =>
      let ⟨a, has, h⟩ := ih h
      ⟨a, Multiset.mem_cons_of_mem has, h⟩

