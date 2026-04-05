import Mathlib

variable {R : Type*} [CommRing R]

theorem quotient' (p : ℕ) [CharP R p] (I : Ideal R) (h : ∀ x : ℕ, (x : R) ∈ I → (x : R) = 0) :
    CharP (R ⧸ I) p where
  cast_eq_zero_iff x := by
    rw [← cast_eq_zero_iff R p x, ← map_natCast (Ideal.Quotient.mk I)]
    refine Ideal.Quotient.eq.trans (?_ : ↑x - 0 ∈ I ↔ _)
    rw [sub_zero]
    exact ⟨h x, fun h' => h'.symm ▸ I.zero_mem⟩

