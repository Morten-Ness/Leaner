import Mathlib

variable {ι k V P : Type*} [Ring k] [AddCommGroup V] [Module k V] [AddTorsor V P]

variable (k) in

variable (k V)

variable {k V}

theorem affineSpan_eq_affineSpan_lineMap_units [Nontrivial k] {s : Set P} {p : P} (hp : p ∈ s)
    (w : s → Units k) :
    affineSpan k (Set.range fun q : s => AffineMap.lineMap p ↑q (w q : k)) = affineSpan k s := by
  have : s = Set.range ((↑) : s → P) := by simp
  conv_rhs =>
    rw [this]
  apply le_antisymm
    <;> intro q hq
    <;> erw [mem_affineSpan_iff_eq_weightedVSubOfPoint_vadd k V _ (⟨p, hp⟩ : s) q] at hq ⊢
    <;> obtain ⟨t, μ, rfl⟩ := hq
    <;> use t
    <;> [use fun x => μ x * ↑(w x); use fun x => μ x * ↑(w x)⁻¹]
    <;> simp [smul_smul]

