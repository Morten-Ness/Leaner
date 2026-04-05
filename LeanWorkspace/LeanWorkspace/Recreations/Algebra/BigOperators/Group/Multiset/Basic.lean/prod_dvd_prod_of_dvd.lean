import Mathlib

variable {F ι κ G M N O : Type*}

theorem prod_dvd_prod_of_dvd [CommMonoid N] {S : Multiset M} (g1 g2 : M → N)
    (h : ∀ a ∈ S, g1 a ∣ g2 a) : (Multiset.map g1 S).prod ∣ (Multiset.map g2 S).prod := by
  apply Multiset.induction_on' S
  · simp
  intro a T haS _ IH
  simp [mul_dvd_mul (h a haS) IH]

