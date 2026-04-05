import Mathlib

variable {R : Type u} {L : Type v} {M : Type w}

variable [CommRing R] [LieRing L] [AddCommGroup M] [Module R M]

variable [LieRingModule L M]

variable (N N' : LieSubmodule R L M)

theorem iSup_induction' {ι} (N : ι → LieSubmodule R L M) {motive : (x : M) → (x ∈ ⨆ i, N i) → Prop}
    (mem : ∀ (i) (x) (hx : x ∈ N i), motive x (LieSubmodule.mem_iSup_of_mem i hx)) (zero : motive 0 (LieSubmodule.zero_mem _))
    (add : ∀ x y hx hy, motive x hx → motive y hy → motive (x + y) (add_mem ‹_› ‹_›)) {x : M}
    (hx : x ∈ ⨆ i, N i) : motive x hx := by
  refine Exists.elim ?_ fun (hx : x ∈ ⨆ i, N i) (hc : motive x hx) => hc
  refine LieSubmodule.iSup_induction N (motive := fun x : M ↦ ∃ (hx : x ∈ ⨆ i, N i), motive x hx) hx
    (fun i x hx => ?_) ?_ fun x y => ?_
  · exact ⟨_, mem _ _ hx⟩
  · exact ⟨_, zero⟩
  · rintro ⟨_, Cx⟩ ⟨_, Cy⟩
    exact ⟨_, add _ _ _ _ Cx Cy⟩

