import Mathlib

variable {ι κ M N G α : Type*}

variable {s s₁ s₂ : Finset ι} {a : ι} {f g : ι → M}

variable [CommMonoid M]

theorem prod_ite_index (p : Prop) [Decidable p] (s t : Finset ι) (f : ι → M) :
    ∏ x ∈ if p then s else t, f x = if p then ∏ x ∈ s, f x else ∏ x ∈ t, f x := apply_ite (fun s => ∏ x ∈ s, f x) _ _ _

