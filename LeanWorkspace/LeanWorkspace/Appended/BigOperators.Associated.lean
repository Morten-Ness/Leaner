import Mathlib

section

variable {ι M M₀ : Type*}

variable [CommMonoidWithZero M₀] {p : M₀}

theorem exists_mem_finset_dvd (hp : Prime p) {s : Finset ι} {f : ι → M₀} :
    p ∣ s.prod f → ∃ i ∈ s, p ∣ f i := Prime.exists_mem_multiset_map_dvd hp

end

section

variable {ι M M₀ : Type*}

variable [CommMonoidWithZero M₀] {p : M₀}

theorem exists_mem_multiset_dvd (hp : Prime p) {s : Multiset M₀} : p ∣ s.prod → ∃ a ∈ s, p ∣ a := Multiset.induction_on s (fun h => (hp.not_dvd_one h).elim) fun a s ih h =>
    have : p ∣ a * s.prod := by simpa using h
    match hp.dvd_or_dvd this with
    | Or.inl h => ⟨a, Multiset.mem_cons_self a s, h⟩
    | Or.inr h =>
      let ⟨a, has, h⟩ := ih h
      ⟨a, Multiset.mem_cons_of_mem has, h⟩

end

section

variable {ι M M₀ : Type*}

variable [CommMonoidWithZero M₀] {p : M₀}

theorem exists_mem_multiset_map_dvd (hp : Prime p) {s : Multiset ι} {f : ι → M₀} :
    p ∣ (s.map f).prod → ∃ a ∈ s, p ∣ f a := fun h => by
  simpa only [exists_prop, Multiset.mem_map, exists_exists_and_eq_and] using
    Prime.exists_mem_multiset_dvd hp h

end

section

variable {ι M M₀ : Type*}

variable [CommMonoid M]

theorem finset_prod_mk {p : Finset ι} {f : ι → M} :
    (∏ i ∈ p, Associates.mk (f i)) = Associates.mk (∏ i ∈ p, f i) := by
  rw [Finset.prod_eq_multiset_prod, ← Function.comp_def, ← Multiset.map_map, Associates.prod_mk,
    ← Finset.prod_eq_multiset_prod]

end

section

variable {ι M M₀ : Type*}

variable [CommMonoid M]

theorem prod_eq_one_iff {p : Multiset (Associates M)} :
    p.prod = 1 ↔ ∀ a ∈ p, (a : Associates M) = 1 := Multiset.induction_on p (by simp)
    (by simp +contextual [mul_eq_one, or_imp, forall_and])

end

section

variable {ι M M₀ : Type*}

variable [CommMonoid M]

theorem prod_mk {p : Multiset M} : (p.map Associates.mk).prod = Associates.mk p.prod := Multiset.induction_on p (by simp) fun a s ih => by simp [ih, Associates.mk_mul_mk]

end

section

variable {ι M M₀ : Type*}

theorem prod_ne_zero_of_prime [CommMonoidWithZero M₀] [NoZeroDivisors M₀] [Nontrivial M₀]
    (s : Multiset M₀) (h : ∀ x ∈ s, Prime x) : s.prod ≠ 0 := Multiset.prod_ne_zero fun h0 => Prime.ne_zero (h 0 h0) rfl

end
