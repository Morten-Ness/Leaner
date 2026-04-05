import Mathlib

variable {α β ι G M N : Type*} [CommMonoid M] [CommMonoid N]

theorem finprod_cond_eq_prod_of_cond_iff (f : α → M) {p : α → Prop} {t : Finset α}
    (h : ∀ {x}, f x ≠ 1 → (p x ↔ x ∈ t)) : (∏ᶠ (i) (_ : p i), f i) = ∏ i ∈ t, f i := by
  set s := { x | p x }
  change ∏ᶠ (i : α) (_ : i ∈ s), f i = ∏ i ∈ t, f i
  have : mulSupport (s.mulIndicator f) ⊆ t := by
    rw [Set.mulSupport_mulIndicator]
    intro x hx
    exact (h hx.2).1 hx.1
  rw [finprod_mem_def, finprod_eq_prod_of_mulSupport_subset _ this]
  refine Finset.prod_congr rfl fun x hx => mulIndicator_apply_eq_self.2 fun hxs => ?_
  contrapose! hxs
  exact (h hxs).2 hx

