import Mathlib

variable {ι κ M N G α : Type*}

variable {s s₁ s₂ : Finset ι} {a : ι} {f g : ι → M}

variable [CommMonoid M]

theorem prod_mem_multiset [DecidableEq ι] (m : Multiset ι) (f : { x // x ∈ m } → M) (g : ι → M)
    (hfg : ∀ x, f x = g x) : ∏ x : { x // x ∈ m }, f x = ∏ x ∈ m.toFinset, g x := by
  refine Finset.prod_bij' (fun x _ ↦ x) (fun x hx ↦ ⟨x, Multiset.mem_toFinset.1 hx⟩) ?_ ?_ ?_ ?_ ?_ <;>
    simp [hfg]

