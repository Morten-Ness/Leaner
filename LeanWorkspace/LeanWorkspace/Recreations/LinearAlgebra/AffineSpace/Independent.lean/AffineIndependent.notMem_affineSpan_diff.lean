import Mathlib

variable (k : Type*) {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]

variable [AddTorsor V P] {ι : Type*}

variable {k}

theorem AffineIndependent.notMem_affineSpan_diff [Nontrivial k] {p : ι → P}
    (ha : AffineIndependent k p) (i : ι) (s : Set ι) : p i ∉ affineSpan k (p '' (s \ {i})) := by
  simp [ha]

