import Mathlib

variable {n R : Type*} [Ring R] [LinearOrder R]

variable {A : Matrix n n R}

theorem IsIrreducible.exists_pos [Nontrivial n]
    (h_irr : IsIrreducible A) (i : n) :
    ∃ j, 0 < A i j := by
  letI : Quiver n := Matrix.toQuiver A
  by_contra h_row
  have no_out : ∀ j : n, IsEmpty (i ⟶ j) :=
    fun j => ⟨fun e => h_row ⟨j, e.down⟩⟩
  obtain ⟨j, hij⟩ := exists_pair_ne n
  obtain ⟨p, hp_pos⟩ := h_irr.connected i j
  have h_le : 1 ≤ p.length := Nat.succ_le_of_lt hp_pos
  have ⟨v, p₁, p₂, _hp_eq, hp₁_len⟩ := p.exists_eq_comp_of_le_length (n := 1) h_le
  have hlen_ne : p₁.length ≠ 0 := by simp [hp₁_len]
  obtain ⟨c, p', e, rfl⟩ := (Quiver.Path.length_ne_zero_iff_eq_cons (p := p₁)).1 (by lia)
  obtain ⟨rfl⟩ : i = c := Quiver.Path.eq_of_length_zero p' (by simp_all)
  exact (no_out _).false e

