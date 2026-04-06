import Mathlib

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable [CommMonoid M] {f g : ι → M}

theorem prod_ite_mem_eq [Fintype ι] (s : Finset ι) (f : ι → M) [DecidablePred (· ∈ s)] :
    (∏ i, if i ∈ s then f i else 1) = ∏ i ∈ s, f i := by
  classical
  simpa [Finset.mem_univ] using
    (Finset.prod_subset (s₁ := s) (s₂ := Finset.univ) (f := f) (by
      intro x hx hxs
      exact False.elim (hxs hx))).symm
