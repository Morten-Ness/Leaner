import Mathlib

theorem sum_sym2_filter_not_isDiag {ι M} [LinearOrder ι] [AddCommMonoid M]
    (s : Finset ι) (p : Sym2 ι → M) :
    ∑ i ∈ s.sym2 with ¬ i.IsDiag, p i = ∑ i ∈ s.offDiag with i.1 < i.2, p s(i.1, i.2) := by
  rw [Finset.sum_sym2_filter_not_isDiag]
