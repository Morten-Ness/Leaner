import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocRing R]

variable [NonAssocRing S] [NonAssocRing T]

theorem exists_list_of_mem_closure {R} [Ring R] {s : Set R} {x : R} (hx : x ∈ Subring.closure s) :
    ∃ L : List (List R), (∀ t ∈ L, ∀ y ∈ t, y ∈ s ∨ y = (-1 : R)) ∧ (L.map List.prod).sum = x := by
  rw [Subring.mem_closure_iff] at hx
  induction hx using AddSubgroup.closure_induction with
  | mem _ hx =>
    obtain ⟨l, hl, h⟩ := Submonoid.exists_list_of_mem_closure hx
    exact ⟨[l], by simp_all⟩
  | zero => exact ⟨[], List.forall_mem_nil _, rfl⟩
  | add _ _ _ _ hL hM =>
    obtain ⟨⟨L, HL1, HL2⟩, ⟨M, HM1, HM2⟩⟩ := And.intro hL hM
    exact ⟨L ++ M, List.forall_mem_append.2 ⟨HL1, HM1⟩, by
      rw [List.map_append, List.sum_append, HL2, HM2]⟩
  | neg _ _ hL =>
    obtain ⟨L, hL⟩ := hL
    exact ⟨L.map (List.cons (-1)),
      List.forall_mem_map.2 fun j hj => List.forall_mem_cons.2 ⟨Or.inr rfl, hL.1 j hj⟩,
      hL.2 ▸
        List.recOn L (by simp)
          (by simp +contextual [List.map_cons, add_comm])⟩

