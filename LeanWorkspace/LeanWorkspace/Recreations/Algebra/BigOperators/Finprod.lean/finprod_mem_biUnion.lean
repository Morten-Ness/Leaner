import Mathlib

variable {α β ι G M N : Type*} [CommMonoid M] [CommMonoid N]

variable {f g : α → M} {a b : α} {s t : Set α}

theorem finprod_mem_biUnion {I : Set ι} {t : ι → Set α} (h : I.PairwiseDisjoint t) (hI : I.Finite)
    (ht : ∀ i ∈ I, (t i).Finite) : ∏ᶠ a ∈ ⋃ x ∈ I, t x, f a = ∏ᶠ i ∈ I, ∏ᶠ j ∈ t i, f j := by
  haveI := hI.fintype
  rw [biUnion_eq_iUnion, finprod_mem_iUnion, ← finprod_set_coe_eq_finprod_mem]
  exacts [fun x y hxy => h x.2 y.2 (Subtype.coe_injective.ne hxy), fun b => ht b b.2]

