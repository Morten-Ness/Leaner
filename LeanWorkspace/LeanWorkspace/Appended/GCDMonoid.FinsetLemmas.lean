import Mathlib

section

variable {ι α : Type*} [CommMonoidWithZero α] [NormalizedGCDMonoid α]

theorem lcm_eq_prod {s : Finset ι} {f : ι → ℕ} (h : Set.Pairwise s <| Nat.Coprime.onFun f) :
    s.lcm f = s.prod f := by
  rw [show Nat.Coprime = IsRelPrime by ext; exact Nat.coprime_iff_isRelPrime] at h
  exact Finset.associated_lcm_prod h |>.eq_of_normalized (normalize_eq _) (normalize_eq _)

end
