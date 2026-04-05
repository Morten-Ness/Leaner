import Mathlib

variable {ι κ G₀ M₀ : Type*} {α : ι → Type*}

variable [CommMonoidWithZero M₀] {p : ι → Prop} [DecidablePred p] {f : ι → M₀} {s : Finset ι}
  {i : ι}

theorem support_prod_subset (s : Finset ι) (f : ι → κ → M₀) :
    support (fun x ↦ ∏ i ∈ s, f i x) ⊆ ⋂ i ∈ s, support (f i) := fun _ hx ↦ Set.mem_iInter₂.2 fun _ hi H ↦ hx <| Finset.prod_eq_zero hi H

