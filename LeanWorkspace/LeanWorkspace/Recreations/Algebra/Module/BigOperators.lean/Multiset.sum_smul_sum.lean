import Mathlib

variable {ι κ α β R M : Type*}

variable [Semiring R] [AddCommMonoid M] [Module R M]

theorem Multiset.sum_smul_sum {s : Multiset R} {t : Multiset M} :
    s.sum • t.sum = ((s ×ˢ t).map fun p : R × M ↦ p.fst • p.snd).sum := by
  induction s using Multiset.induction with
  | empty => simp
  | cons a s ih => simp [add_smul, ih, ← Multiset.smul_sum]

