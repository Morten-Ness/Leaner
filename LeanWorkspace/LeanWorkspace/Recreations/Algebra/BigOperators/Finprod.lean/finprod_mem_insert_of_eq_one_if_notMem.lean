import Mathlib

variable {α β ι G M N : Type*} [CommMonoid M] [CommMonoid N]

variable {f g : α → M} {a b : α} {s t : Set α}

theorem finprod_mem_insert_of_eq_one_if_notMem (h : a ∉ s → f a = 1) :
    ∏ᶠ i ∈ insert a s, f i = ∏ᶠ i ∈ s, f i := by
  refine finprod_mem_inter_mulSupport_eq' _ _ _ fun x hx => ⟨?_, Or.inr⟩
  rintro (rfl | hxs)
  exacts [not_imp_comm.1 h hx, hxs]

