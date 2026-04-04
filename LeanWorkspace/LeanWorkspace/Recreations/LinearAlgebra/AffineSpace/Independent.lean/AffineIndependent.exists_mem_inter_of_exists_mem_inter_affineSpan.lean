import Mathlib

variable (k : Type*) {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]

variable [AddTorsor V P] {ι : Type*}

variable {k}

theorem AffineIndependent.exists_mem_inter_of_exists_mem_inter_affineSpan [Nontrivial k] {p : ι → P}
    (ha : AffineIndependent k p) {s1 s2 : Set ι} {p0 : P} (hp0s1 : p0 ∈ affineSpan k (p '' s1))
    (hp0s2 : p0 ∈ affineSpan k (p '' s2)) : ∃ i : ι, i ∈ s1 ∩ s2 := by
  have hp0' : p0 ∈ affineSpan k (p '' s1) ⊓ affineSpan k (p '' s2) := ⟨hp0s1, hp0s2⟩
  rw [ha.inf_affineSpan_eq_affineSpan_inter] at hp0'
  rw [← Set.Nonempty]
  by_contra he
  rw [Set.not_nonempty_iff_eq_empty] at he
  simp [he, AffineSubspace.notMem_bot] at hp0'

