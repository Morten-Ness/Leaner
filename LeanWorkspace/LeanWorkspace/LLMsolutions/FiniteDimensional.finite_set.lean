FAIL
import Mathlib

variable {ι : Type u₁} {k : Type u₂} {V : Type u₃} {P : Type u₄}

variable [AddCommGroup V] [AddTorsor V P]

variable [DivisionRing k] [Module k V]

theorem finite_set [FiniteDimensional k V] {s : Set ι} (b : AffineBasis s k P) :
    s.Finite := by
  classical
  by_cases hs : s.Nonempty
  · let i : s := Classical.choice hs
    let vb := b.basisOf i
    exact vb.finite
  · exact Set.not_nonempty_iff_eq_empty.mp hs |> by
      intro h
      simpa [h] using Set.toFinite (∅ : Set ι)
