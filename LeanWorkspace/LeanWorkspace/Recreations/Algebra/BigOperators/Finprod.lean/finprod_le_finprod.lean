import Mathlib

variable {α β ι G M N : Type*} [CommMonoid M] [CommMonoid N]

variable {f g : α → M} {a b : α} {s t : Set α}

theorem finprod_le_finprod {M : Type*} [CommMonoidWithZero M] [PartialOrder M] [ZeroLEOneClass M]
    [PosMulMono M] {f g : α → M} (hf : HasFiniteMulSupport f) (hf₀ : ∀ a, 0 ≤ f a)
    (hg : HasFiniteMulSupport g) (h : f ≤ g) :
    ∏ᶠ a, f a ≤ ∏ᶠ a, g a := by
  have : Fintype ↑(f.mulSupport ∪ g.mulSupport) := (hf.union hg).fintype
  let s := (f.mulSupport ∪ g.mulSupport).toFinset
  rw [finprod_eq_finset_prod_of_mulSupport_subset f (show f.mulSupport ⊆ s by grind),
    finprod_eq_finset_prod_of_mulSupport_subset g (show g.mulSupport ⊆ s by grind)]
  exact Finset.prod_le_prod (fun i _ ↦ hf₀ i) fun i _ ↦ h i

