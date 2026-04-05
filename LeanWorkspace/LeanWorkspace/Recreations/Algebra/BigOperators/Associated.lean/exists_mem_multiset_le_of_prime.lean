import Mathlib

variable {ι M M₀ : Type*}

variable [CommMonoidWithZero M₀]

theorem exists_mem_multiset_le_of_prime {s : Multiset (Associates M₀)} {p : Associates M₀}
    (hp : Prime p) : p ≤ s.prod → ∃ a ∈ s, p ≤ a := Multiset.induction_on s (fun ⟨_, eq⟩ => (hp.ne_one (mul_eq_one.1 eq.symm).1).elim)
    fun a s ih h =>
    have : p ≤ a * s.prod := by simpa using h
    match Prime.le_or_le hp this with
    | Or.inl h => ⟨a, Multiset.mem_cons_self a s, h⟩
    | Or.inr h =>
      let ⟨a, has, h⟩ := ih h
      ⟨a, Multiset.mem_cons_of_mem has, h⟩

