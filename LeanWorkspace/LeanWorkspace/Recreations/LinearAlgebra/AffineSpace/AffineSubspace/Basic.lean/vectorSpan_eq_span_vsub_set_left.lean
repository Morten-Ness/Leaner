import Mathlib

variable (k : Type*) {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

variable {ι : Type*}

theorem vectorSpan_eq_span_vsub_set_left {s : Set P} {p : P} (hp : p ∈ s) :
    vectorSpan k s = Submodule.span k ((p -ᵥ ·) '' s) := by
  rw [vectorSpan_def]
  refine le_antisymm ?_ (Submodule.span_mono ?_)
  · rw [Submodule.span_le]
    rintro v ⟨p₁, hp₁, p₂, hp₂, hv⟩
    simp_rw [← vsub_sub_vsub_cancel_left p₁ p₂ p] at hv
    rw [← hv, SetLike.mem_coe, Submodule.mem_span]
    exact fun m hm => Submodule.sub_mem _ (hm ⟨p₂, hp₂, rfl⟩) (hm ⟨p₁, hp₁, rfl⟩)
  · rintro v ⟨p₂, hp₂, hv⟩
    exact ⟨p, hp, p₂, hp₂, hv⟩

