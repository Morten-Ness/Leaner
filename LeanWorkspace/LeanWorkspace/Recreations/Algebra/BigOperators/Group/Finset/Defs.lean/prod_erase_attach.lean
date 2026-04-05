import Mathlib

variable {ι κ M N G α : Type*}

variable {s s₁ s₂ : Finset ι} {a : ι} {f g : ι → M}

variable [CommMonoid M]

theorem prod_erase_attach [DecidableEq ι] {s : Finset ι} (f : ι → M) (i : ↑s) :
    ∏ j ∈ s.attach.erase i, f ↑j = ∏ j ∈ s.erase ↑i, f j := by
  rw [← Function.Embedding.coe_subtype, ← Finset.prod_map]
  simp [attach_map_val]

