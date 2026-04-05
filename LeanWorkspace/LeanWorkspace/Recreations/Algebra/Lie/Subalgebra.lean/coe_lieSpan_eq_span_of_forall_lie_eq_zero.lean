import Mathlib

variable (R : Type u) (L : Type v) [CommRing R] [LieRing L] [LieAlgebra R L]

variable {L₂ : Type w} [LieRing L₂] [LieAlgebra R L₂]

variable (f : L →ₗ⁅R⁆ L₂)

variable (K K' : LieSubalgebra R L) (K₂ : LieSubalgebra R L₂)

variable (R L) (s : Set L)

theorem coe_lieSpan_eq_span_of_forall_lie_eq_zero
    {s : Set L} (hs : ∀ᵉ (x ∈ s) (y ∈ s), ⁅x, y⁆ = 0) :
    LieSubalgebra.lieSpan R L s = span R s := by
  suffices ∀ {x y}, x ∈ span R s → y ∈ span R s → ⁅x, y⁆ ∈ span R s by
    refine le_antisymm ?_ LieSubalgebra.submodule_span_le_lieSpan
    change _ ≤ ({ span R s with lie_mem' := this } : LieSubalgebra R L)
    rw [LieSubalgebra.lieSpan_le]
    exact subset_span
  intro x y hx hy
  induction hx, hy using span_induction₂ with
  | mem_mem x y hx hy => simp [hs x hx y hy]
  | zero_left y hy => simp
  | zero_right x hx => simp
  | add_left x y z _ _ _ hx hy => simp [LieSubalgebra.add_mem hx hy]
  | add_right x y z _ _ _ hx hy => simp [LieSubalgebra.add_mem hx hy]
  | smul_left r x y _ _ h => simp [LieSubalgebra.smul_mem _ r h]
  | smul_right r x y _ _ h => simp [LieSubalgebra.smul_mem _ r h]

