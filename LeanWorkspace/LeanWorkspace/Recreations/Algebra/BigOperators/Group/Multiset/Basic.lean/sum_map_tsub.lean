import Mathlib

variable {F ι κ G M N O : Type*}

theorem sum_map_tsub [AddCommMonoid M] [PartialOrder M] [ExistsAddOfLE M]
    [AddLeftMono M] [AddLeftReflectLE M] [Sub M]
    [OrderedSub M] (l : Multiset ι) {f g : ι → M} (hfg : ∀ x ∈ l, g x ≤ f x) :
    (l.map fun x ↦ f x - g x).sum = (l.map f).sum - (l.map g).sum := eq_tsub_of_add_eq <| by
    rw [← sum_map_add]
    congr 1
    exact map_congr rfl fun x hx => tsub_add_cancel_of_le <| hfg _ hx

