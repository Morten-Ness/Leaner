import Mathlib

variable (k : Type*) {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]

variable [AddTorsor V P] {ι : Type*}

variable {k}

variable {s : Finset ι} {w w₁ w₂ : ι → k} {p : ι → V}

theorem affineIndependent_iff {ι} {p : ι → V} :
    AffineIndependent k p ↔
      ∀ (s : Finset ι) (w : ι → k), s.sum w = 0 → ∑ e ∈ s, w e • p e = 0 → ∀ e ∈ s, w e = 0 := forall₃_congr fun s w hw => by simp [s.weightedVSub_eq_linear_combination hw]

