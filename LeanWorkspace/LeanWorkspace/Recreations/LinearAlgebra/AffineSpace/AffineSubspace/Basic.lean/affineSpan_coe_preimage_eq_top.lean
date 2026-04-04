import Mathlib

variable (k : Type*) {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

variable {ι : Type*}

variable {k}

theorem affineSpan_coe_preimage_eq_top (A : Set P) [Nonempty A] :
    affineSpan k (((↑) : affineSpan k A → P) ⁻¹' A) = ⊤ := by
  rw [eq_top_iff]
  rintro ⟨x, hx⟩ -
  refine affineSpan_induction' (fun y hy ↦ ?_) (fun c u hu v hv w hw ↦ ?_) hx
  · exact subset_affineSpan _ _ hy
  · exact AffineSubspace.smul_vsub_vadd_mem _ _

