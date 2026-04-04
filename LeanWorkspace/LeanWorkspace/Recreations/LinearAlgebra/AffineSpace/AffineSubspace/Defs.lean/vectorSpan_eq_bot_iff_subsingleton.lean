import Mathlib

variable (k : Type*) {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]

variable [AddTorsor V P]

variable (P) in

theorem vectorSpan_eq_bot_iff_subsingleton {s : Set P} : vectorSpan k s = ⊥ ↔ s.Subsingleton := by
  refine ⟨fun h ↦ ?_, vectorSpan_of_subsingleton _⟩
  by_contra hns
  rw [Set.not_subsingleton_iff] at hns
  obtain ⟨p, hp, q, hq, hpq⟩ := hns
  have hpq' := vsub_mem_vectorSpan k hp hq
  simp_all

