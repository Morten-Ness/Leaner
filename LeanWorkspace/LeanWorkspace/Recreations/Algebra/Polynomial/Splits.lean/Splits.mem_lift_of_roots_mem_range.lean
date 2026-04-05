import Mathlib

variable {R : Type*}

variable [CommRing R] {f g : R[X]} {A B : Type*} [CommRing A] [CommRing B]
  [IsDomain A] [IsDomain B] [Algebra R A] [Algebra R B]

variable [IsDomain R]

theorem Splits.mem_lift_of_roots_mem_range (hf : f.Splits) (hm : f.Monic)
    {S : Type*} [Ring S] (i : S →+* R) (hr : ∀ a ∈ f.roots, a ∈ i.range) :
    f ∈ Polynomial.lifts i := by
  rw [hf.eq_prod_roots_of_monic hm, lifts_iff_liftsRing]
  refine Subring.multiset_prod_mem _ _ fun g hg => ?_
  obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.mp hg
  exact Subring.sub_mem _ (X_mem_lifts i) (C'_mem_lifts (hr x hx))

