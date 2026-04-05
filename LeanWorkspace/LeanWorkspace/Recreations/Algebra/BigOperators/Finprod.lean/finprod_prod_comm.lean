import Mathlib

variable {α β ι G M N : Type*} [CommMonoid M] [CommMonoid N]

variable {f g : α → M} {a b : α} {s t : Set α}

theorem finprod_prod_comm (s : Finset β) (f : α → β → M)
    (h : ∀ b ∈ s, HasFiniteMulSupport fun a ↦ f a b) :
    (∏ᶠ a : α, ∏ b ∈ s, f a b) = ∏ b ∈ s, ∏ᶠ a : α, f a b := by
  have hU :
    (mulSupport fun a => ∏ b ∈ s, f a b) ⊆
      (s.finite_toSet.biUnion fun b hb => h b (Finset.mem_coe.1 hb)).toFinset := by
    rw [Finite.coe_toFinset]
    intro x hx
    simp only [exists_prop, mem_iUnion, Ne, mem_mulSupport, Finset.mem_coe]
    contrapose! hx
    rw [mem_mulSupport, not_not, Finset.prod_congr rfl hx, Finset.prod_const_one]
  rw [finprod_eq_prod_of_mulSupport_subset _ hU, Finset.prod_comm]
  refine Finset.prod_congr rfl fun b hb => (finprod_eq_prod_of_mulSupport_subset _ ?_).symm
  intro a ha
  simp only [Finite.coe_toFinset, mem_iUnion]
  exact ⟨b, hb, ha⟩

