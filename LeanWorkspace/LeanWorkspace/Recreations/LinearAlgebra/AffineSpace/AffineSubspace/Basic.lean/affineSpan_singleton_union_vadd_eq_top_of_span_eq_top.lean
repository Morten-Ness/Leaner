import Mathlib

variable (k : Type*) {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

variable {ι : Type*}

variable {k}

theorem affineSpan_singleton_union_vadd_eq_top_of_span_eq_top {s : Set V} (p : P)
    (h : Submodule.span k (Set.range ((↑) : s → V)) = ⊤) :
    affineSpan k ({p} ∪ (fun v => v +ᵥ p) '' s) = ⊤ := by
  convert ext_of_direction_eq _
      ⟨p, mem_affineSpan k (Set.mem_union_left _ (Set.mem_singleton _)), mem_top k V p⟩
  rw [direction_affineSpan, direction_top,
    vectorSpan_eq_span_vsub_set_right k (Set.mem_union_left _ (Set.mem_singleton _) : p ∈ _),
    eq_top_iff, ← h]
  apply Submodule.span_mono
  rintro v ⟨v', rfl⟩
  use (v' : V) +ᵥ p
  simp

