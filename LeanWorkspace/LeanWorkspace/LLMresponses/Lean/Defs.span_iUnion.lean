import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]
  [S : AddTorsor V P] {ι : Sort*}

variable (k V)

variable (P)

variable {k V P}

variable (k V) {p₁ p₂ : P}

theorem span_iUnion {ι : Type*} (s : ι → Set P) :
    affineSpan k (⋃ i, s i) = ⨆ i, affineSpan k (s i) := by
  classical
  refine le_antisymm ?_ ?_
  · refine affineSpan_le.2 ?_
    intro p hp
    rcases Set.mem_iUnion.mp hp with ⟨i, hi⟩
    exact le_iSup (fun i => affineSpan k (s i)) i (subset_affineSpan k (s i) hi)
  · refine iSup_le ?_
    intro i
    exact affineSpan_mono k (Set.subset_iUnion s i)
