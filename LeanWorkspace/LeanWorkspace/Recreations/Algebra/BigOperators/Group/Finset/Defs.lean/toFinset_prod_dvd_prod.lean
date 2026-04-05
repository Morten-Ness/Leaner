import Mathlib

variable {ι κ M N G α : Type*}

variable {s s₁ s₂ : Finset ι} {a : ι} {f g : ι → M}

variable [DecidableEq α]

theorem toFinset_prod_dvd_prod [DecidableEq M] [CommMonoid M] (S : Multiset M) :
    S.toFinset.prod id ∣ S.prod := by
  rw [Finset.prod_eq_multiset_prod]
  refine Multiset.prod_dvd_prod_of_le ?_
  simp [Multiset.dedup_le S]

