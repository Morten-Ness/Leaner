import Mathlib

open scoped Finset

variable {ι κ M G : Type*}

variable [AddCommMonoid M] [LinearOrder M] [CanonicallyOrderedAdd M]
  [Sub M] [AddLeftReflectLE M] [OrderedSub M] {s : Finset ι} {t : Finset κ}

theorem add_sup'' (hs : s.Nonempty) (f : ι → M) (a : M) :
    a + s.sup' hs f = s.sup' hs fun i ↦ a + f i := by simp_rw [add_comm a, Finset.sup'_add']

