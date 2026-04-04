import Mathlib

variable (k : Type*) {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

variable {ι : Type*}

variable {k}

variable (k)

theorem affineSpan_le_toAffineSubspace_span {s : Set V} :
    affineSpan k s ≤ (Submodule.span k s).toAffineSubspace := by
  intro x hx
  simp only [Submodule.mem_toAffineSubspace]
  induction hx using affineSpan_induction' with
  | mem x hx => exact Submodule.subset_span hx
  | smul_vsub_vadd c u _ v _ w _ hu hv hw =>
    simp only [vsub_eq_sub, vadd_eq_add]
    apply Submodule.add_mem _ _ hw
    exact Submodule.smul_mem _ _ (Submodule.sub_mem _ hu hv)

