import Mathlib

open scoped Finset

variable {ι κ M G : Type*}

variable [AddCommMonoid M] [LinearOrder M] [CanonicallyOrderedAdd M]
  [Sub M] [AddLeftReflectLE M] [OrderedSub M] {s : Finset ι} {t : Finset κ}

variable [OrderBot M]

theorem sup_add_sup (hs : s.Nonempty) (ht : t.Nonempty) (f : ι → M) (g : κ → M) :
    s.sup f + t.sup g = (s ×ˢ t).sup fun ij ↦ f ij.1 + g ij.2 := by
  simp only [Finset.sup_add hs, Finset.add_sup ht, Finset.sup_product_left]

