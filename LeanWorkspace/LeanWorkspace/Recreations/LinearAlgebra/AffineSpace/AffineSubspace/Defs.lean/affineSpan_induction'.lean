import Mathlib

variable (k : Type*) {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

variable {ι : Type*}

variable {k}

theorem affineSpan_induction' {s : Set P} {p : ∀ x, x ∈ affineSpan k s → Prop}
    (mem : ∀ (y) (hys : y ∈ s), p y (subset_affineSpan k _ hys))
    (smul_vsub_vadd : ∀ (c : k) (u hu v hv w hw), p u hu → p v hv → p w hw →
      p (c • (u -ᵥ v) +ᵥ w) (AffineSubspace.smul_vsub_vadd_mem _ _ hu hv hw))
    {x : P} (h : x ∈ affineSpan k s) : p x h := by
  suffices ∃ (hx : x ∈ affineSpan k s), p x hx from this.elim fun hx hc ↦ hc
  -- TODO: `induction h using affineSpan_induction` gives the error:
  -- extra targets for '@affineSpan_induction'
  -- It seems that the `induction` tactic has decided to ignore the clause
  -- `using affineSpan_induction` and use `Exists.rec` instead.
  refine affineSpan_induction h ?mem ?smul_vsub_vadd
  · exact fun y hy ↦ ⟨subset_affineSpan _ _ hy, mem y hy⟩
  · exact fun c u v w hu hv hw ↦
      hu.elim fun hu' hu ↦ hv.elim fun hv' hv ↦ hw.elim fun hw' hw ↦
        ⟨AffineSubspace.smul_vsub_vadd_mem _ _ hu' hv' hw',
              smul_vsub_vadd _ _ _ _ _ _ _ hu hv hw⟩

