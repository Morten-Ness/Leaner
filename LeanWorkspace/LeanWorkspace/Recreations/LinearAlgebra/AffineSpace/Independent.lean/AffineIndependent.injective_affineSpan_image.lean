import Mathlib

variable (k : Type*) {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]

variable [AddTorsor V P] {ι : Type*}

variable {k}

theorem AffineIndependent.injective_affineSpan_image [Nontrivial k] {p : ι → P}
    (ha : AffineIndependent k p) : Function.Injective fun (s : Set ι) ↦ affineSpan k (p '' s) := by
  by_contra hn
  rw [not_injective_iff] at hn
  obtain ⟨s₁, s₂, hs₁₂, hne⟩ := hn
  apply hne
  ext i
  simp_rw [← ha.mem_affineSpan_iff, hs₁₂]

