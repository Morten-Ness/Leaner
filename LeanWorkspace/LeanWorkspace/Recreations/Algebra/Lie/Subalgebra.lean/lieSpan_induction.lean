import Mathlib

variable (R : Type u) (L : Type v) [CommRing R] [LieRing L] [LieAlgebra R L]

variable {L₂ : Type w} [LieRing L₂] [LieAlgebra R L₂]

variable (f : L →ₗ⁅R⁆ L₂)

variable (K K' : LieSubalgebra R L) (K₂ : LieSubalgebra R L₂)

variable (R L) (s : Set L)

theorem lieSpan_induction {p : (x : L) → x ∈ LieSubalgebra.lieSpan R L s → Prop}
    (mem : ∀ (x) (h : x ∈ s), p x (LieSubalgebra.subset_lieSpan h))
    (zero : p 0 (LieSubalgebra.zero_mem _))
    (add : ∀ x y hx hy, p x hx → p y hy → p (x + y) (LieSubalgebra.add_mem _ ‹_› ‹_›))
    (smul : ∀ (a : R) (x hx), p x hx → p (a • x) (LieSubalgebra.smul_mem _ _ ‹_›)) {x}
    (lie : ∀ x y hx hy, p x hx → p y hy → p (⁅x, y⁆) (LieSubalgebra.lie_mem _ ‹_› ‹_›))
    (hx : x ∈ LieSubalgebra.lieSpan R L s) : p x hx := by
  let p : LieSubalgebra R L :=
    { carrier := { x | ∃ hx, p x hx }
      add_mem' := fun ⟨_, hpx⟩ ⟨_, hpy⟩ ↦ ⟨_, add _ _ _ _ hpx hpy⟩
      zero_mem' := ⟨_, zero⟩
      smul_mem' := fun r ↦ fun ⟨_, hpx⟩ ↦ ⟨_, smul r _ _ hpx⟩
      lie_mem' := fun ⟨_, hpx⟩ ⟨_, hpy⟩ ↦ ⟨_, lie _ _ _ _ hpx hpy⟩ }
  exact LieSubalgebra.lieSpan_le (K := p) |>.mpr (fun y hy ↦ ⟨LieSubalgebra.subset_lieSpan hy, mem y hy⟩) hx |>.elim fun _ ↦ id

