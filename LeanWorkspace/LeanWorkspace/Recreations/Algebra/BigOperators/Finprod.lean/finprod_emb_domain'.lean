import Mathlib

variable {α β ι G M N : Type*} [CommMonoid M] [CommMonoid N]

variable {f g : α → M} {a b : α} {s t : Set α}

theorem finprod_emb_domain' {f : α → β} (hf : Function.Injective f) [DecidablePred (· ∈ Set.range f)]
    (g : α → M) :
    (∏ᶠ b : β, if h : b ∈ Set.range f then g (Classical.choose h) else 1) = ∏ᶠ a : α, g a := by
  simp_rw [← finprod_eq_dif]
  rw [finprod_dmem, finprod_mem_range hf, finprod_congr fun a => _]
  intro a
  rw [dif_pos (Set.mem_range_self a), hf (Classical.choose_spec (Set.mem_range_self a))]

