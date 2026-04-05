import Mathlib

variable {ι κ M N G α : Type*}

variable {s s₁ s₂ : Finset ι} {a : ι} {f g : ι → M}

theorem sum_nat_mod (s : Finset ι) (n : ℕ) (f : ι → ℕ) :
    (∑ i ∈ s, f i) % n = (∑ i ∈ s, f i % n) % n := (Multiset.sum_nat_mod _ _).trans <| by rw [Finset.sum, Multiset.map_map]; rfl

