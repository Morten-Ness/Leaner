import Mathlib

variable {M A B : Type*}

theorem mem_closure_pair {A : Type*} [CommMonoid A] (a b c : A) :
    c ∈ Submonoid.closure ({a, b} : Set A) ↔ ∃ m n : ℕ, a ^ m * b ^ n = c := by
  rw [← Set.singleton_union, Submonoid.closure_union, Submonoid.mem_sup]
  simp_rw [Submonoid.mem_closure_singleton, exists_exists_eq_and]

