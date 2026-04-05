import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocSemiring R] (M : Submonoid R)

variable [NonAssocSemiring S] [NonAssocSemiring T]

theorem mem_closure_iff_exists_list {R} [Semiring R] {s : Set R} {x} :
    x ∈ Subsemiring.closure s ↔ ∃ L : List (List R), (∀ t ∈ L, ∀ y ∈ t, y ∈ s) ∧ (L.map List.prod).sum = x := by
  constructor
  · intro hx
    rw [Subsemiring.mem_closure_iff] at hx
    induction hx using AddSubmonoid.closure_induction with
    | mem x hx =>
      suffices ∃ t : List R, (∀ y ∈ t, y ∈ s) ∧ t.prod = x from
        let ⟨t, ht1, ht2⟩ := this
        ⟨[t], List.forall_mem_singleton.2 ht1, by
          rw [List.map_singleton, List.sum_singleton, ht2]⟩
      induction hx using Submonoid.closure_induction with
      | mem x hx => exact ⟨[x], List.forall_mem_singleton.2 hx, List.prod_singleton⟩
      | one => exact ⟨[], List.forall_mem_nil _, rfl⟩
      | mul x y _ _ ht hu =>
        obtain ⟨⟨t, ht1, ht2⟩, ⟨u, hu1, hu2⟩⟩ := And.intro ht hu
        exact ⟨t ++ u, List.forall_mem_append.2 ⟨ht1, hu1⟩, by rw [List.prod_append, ht2, hu2]⟩
    | zero => exact ⟨[], List.forall_mem_nil _, rfl⟩
    | add x y _ _ hL hM =>
      obtain ⟨⟨L, HL1, HL2⟩, ⟨M, HM1, HM2⟩⟩ := And.intro hL hM
      exact ⟨L ++ M, List.forall_mem_append.2 ⟨HL1, HM1⟩, by
        rw [List.map_append, List.sum_append, HL2, HM2]⟩
  · rintro ⟨L, HL1, rfl⟩
    exact
      Subsemiring.list_sum_mem fun r hr =>
        let ⟨t, ht1, ht2⟩ := List.mem_map.1 hr
        ht2 ▸ list_prod_mem _ fun y hy => Subsemiring.subset_closure <| HL1 t ht1 y hy

