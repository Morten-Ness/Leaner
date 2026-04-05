import Mathlib

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

theorem card_disjiUnion (s : Finset ι) (t : ι → Finset M) (h) :
    #(s.disjiUnion t h) = ∑ a ∈ s, #(t a) := Multiset.card_bind _ _

