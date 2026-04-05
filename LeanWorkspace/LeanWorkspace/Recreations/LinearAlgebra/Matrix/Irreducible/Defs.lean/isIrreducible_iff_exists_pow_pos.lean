import Mathlib

variable {n R : Type*} [Ring R] [LinearOrder R]

variable {A : Matrix n n R}

theorem isIrreducible_iff_exists_pow_pos
    [Fintype n] [IsOrderedRing R] [PosMulStrictMono R] [Nontrivial R] [DecidableEq n]
    (hA : ∀ i j, 0 ≤ A i j) :
    IsIrreducible A ↔ ∀ i j, ∃ k > 0, 0 < (A ^ k) i j := by
  letI : Quiver n := Matrix.toQuiver A
  constructor
  · intro h_irr i j
    obtain ⟨p, hp_len⟩ := h_irr.2 i j
    refine ⟨p.length, hp_len, ?_⟩
    have : Nonempty {q : Path i j // q.length = p.length} := ⟨⟨p, rfl⟩⟩
    have hpos :=
      (Matrix.pow_apply_pos_iff_nonempty_path (A := A) hA p.length i j).2 this
    simpa using hpos
  · intro h_exists
    constructor
    · exact hA
    · intro i j
      obtain ⟨k, hk_pos, hk_entry⟩ := h_exists i j
      obtain ⟨⟨p, rfl⟩⟩ :=
        (Matrix.pow_apply_pos_iff_nonempty_path (A := A) hA k i j).mp hk_entry
      exact ⟨p, hk_pos⟩

