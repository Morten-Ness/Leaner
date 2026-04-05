import Mathlib

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable [CommMonoid M] {f g : ι → M}

theorem _root_.IsCompl.prod_mul_prod [Fintype ι] {s t : Finset ι} (h : IsCompl s t) (f : ι → M) :
    (∏ i ∈ s, f i) * ∏ i ∈ t, f i = ∏ i, f i := (Finset.prod_disjUnion h.disjoint).symm.trans <| by
    classical rw [Finset.disjUnion_eq_union, ← Finset.sup_eq_union, h.sup_eq_top]; rfl

