import Mathlib

variable {R : Type u} {L : Type v} {M : Type w}

variable [CommRing R] [LieRing L] [AddCommGroup M] [Module R M]

variable [LieRingModule L M]

variable (N N' : LieSubmodule R L M)

variable (R L) (s : Set M)

theorem lieSpan_induction {p : (x : M) → x ∈ LieSubmodule.lieSpan R L s → Prop}
    (mem : ∀ (x) (h : x ∈ s), p x (LieSubmodule.subset_lieSpan h))
    (zero : p 0 (LieSubmodule.zero_mem _))
    (add : ∀ x y hx hy, p x hx → p y hy → p (x + y) (add_mem ‹_› ‹_›))
    (smul : ∀ (a : R) (x hx), p x hx → p (a • x) (SMulMemClass.smul_mem _ hx)) {x}
    (lie : ∀ (x : L) (y hy), p y hy → p (⁅x, y⁆) (LieSubmodule.lie_mem _ ‹_›))
    (hx : x ∈ LieSubmodule.lieSpan R L s) : p x hx := by
  let p : LieSubmodule R L M :=
    { carrier := { x | ∃ hx, p x hx }
      add_mem' := fun ⟨_, hpx⟩ ⟨_, hpy⟩ ↦ ⟨_, add _ _ _ _ hpx hpy⟩
      zero_mem' := ⟨_, zero⟩
      smul_mem' := fun r ↦ fun ⟨_, hpx⟩ ↦ ⟨_, smul r _ _ hpx⟩
      lie_mem := fun ⟨_, hpy⟩ ↦ ⟨_, lie _ _ _ hpy⟩ }
  exact LieSubmodule.lieSpan_le (N := p) |>.mpr (fun y hy ↦ ⟨LieSubmodule.subset_lieSpan hy, mem y hy⟩) hx |>.elim fun _ ↦ id

