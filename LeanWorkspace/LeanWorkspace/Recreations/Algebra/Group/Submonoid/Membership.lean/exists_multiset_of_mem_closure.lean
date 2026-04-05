import Mathlib

variable {M A B : Type*}

variable [Monoid M] {a : M}

theorem exists_multiset_of_mem_closure {M : Type*} [CommMonoid M] {s : Set M} {x : M}
    (hx : x ∈ closure s) : ∃ l : Multiset M, (∀ y ∈ l, y ∈ s) ∧ l.prod = x := by
  obtain ⟨l, h1, h2⟩ := Submonoid.exists_list_of_mem_closure hx
  exact ⟨l, h1, (Multiset.prod_coe l).trans h2⟩

