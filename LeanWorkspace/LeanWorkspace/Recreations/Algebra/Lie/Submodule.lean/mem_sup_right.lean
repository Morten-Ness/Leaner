import Mathlib

variable {R : Type u} {L : Type v} {M : Type w}

variable [CommRing R] [LieRing L] [AddCommGroup M] [Module R M]

variable [LieRingModule L M]

variable (N N' : LieSubmodule R L M)

theorem mem_sup_right {x : M} (hx : x ∈ N') : x ∈ N ⊔ N' := (LieSubmodule.mem_sup _ _ _).mpr ⟨0, by simp, x, hx, by simp⟩

nonrec theorem eq_bot_iff : N = ⊥ ↔ ∀ m : M, m ∈ N → m = 0 := by rw [eq_bot_iff]; exact Iff.rfl

