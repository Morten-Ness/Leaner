import Mathlib

variable {ι α β M N G k R : Type*}

variable [CommMonoid M] [CommMonoid N] [Preorder N]

variable {f g : ι → N} {s t : Finset ι}

theorem one_lt_prod_iff_of_one_le {ι : Type u_1} {N : Type u_5} [CommMonoid N] [PartialOrder N]
    {f : ι → N} {s : Finset ι} [MulLeftMono N] (hf : ∀ x ∈ s, 1 ≤ f x) :
    1 < ∏ x ∈ s, f x ↔ ∃ x ∈ s, 1 < f x := by
  have hsum : 1 ≤ ∏ x ∈ s, f x := Finset.one_le_prod' hf
  rw [hsum.lt_iff_ne', Ne, Finset.prod_eq_one_iff_of_one_le' hf, not_forall]
  simp +contextual [← exists_prop, -exists_const_iff, hf _ _ |>.lt_iff_ne']

