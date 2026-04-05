import Mathlib

open scoped Finset

variable {ι κ M N R α : Type*}

variable [Finite ι] [DecidableEq ι] {M : ι → Type*}

theorem eqOn_finsetProd {ι α β : Type*} [CommMonoid α]
    {s : Set β} {f f' : ι → β → α} (h : ∀ (i : ι), Set.EqOn (f i) (f' i) s) (v : Finset ι) :
    Set.EqOn (∏ i ∈ v, f i) (∏ i ∈ v, f' i) s := fun t ht => by simp [funext fun i ↦ h i ht]

