import Mathlib

variable {ι κ M N G α : Type*}

variable {s s₁ s₂ : Finset ι} {a : ι} {f g : ι → M}

theorem card_sum (s : Finset ι) (f : ι → Multiset α) : card (∑ i ∈ s, f i) = ∑ i ∈ s, card (f i) := map_sum cardHom ..

