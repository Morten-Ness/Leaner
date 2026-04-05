import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {a b : R} {n : ℕ}

variable [CommRing R] [IsDomain R] {p q : R[X]}

theorem roots_eq_zero_iff_isRoot_eq_bot (hp0 : p ≠ 0) : p.roots = 0 ↔ p.IsRoot = ⊥ := by
  refine ⟨fun h ↦ ?_, fun h ↦ eq_zero_of_forall_notMem fun x hx ↦ h ▸ Polynomial.mem_roots hp0 |>.mp hx⟩
  ext a
  simp only [Pi.bot_apply, Prop.bot_eq_false, Polynomial.mem_roots hp0 |>.not.mp <| by simp [h]]

