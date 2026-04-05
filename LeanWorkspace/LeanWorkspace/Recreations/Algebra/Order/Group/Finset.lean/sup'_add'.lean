import Mathlib

open scoped Finset

variable {ι κ M G : Type*}

variable [AddCommMonoid M] [LinearOrder M] [CanonicallyOrderedAdd M]
  [Sub M] [AddLeftReflectLE M] [OrderedSub M] {s : Finset ι} {t : Finset κ}

theorem sup'_add' (s : Finset ι) (f : ι → M) (a : M) (hs : s.Nonempty) :
    s.sup' hs f + a = s.sup' hs fun i ↦ f i + a := by
  apply le_antisymm
  · apply add_le_of_le_tsub_right_of_le
    · exact Finset.le_sup'_of_le _ hs.choose_spec le_add_self
    · exact Finset.sup'_le _ _ fun i hi ↦ le_tsub_of_add_le_right (Finset.le_sup' (f · + a) hi)
  · exact Finset.sup'_le _ _ fun i hi ↦ by grw [← Finset.le_sup' _ hi]

