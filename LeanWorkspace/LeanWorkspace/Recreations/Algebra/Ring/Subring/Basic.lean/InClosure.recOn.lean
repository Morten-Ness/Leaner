import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocRing R]

variable [NonAssocRing S] [NonAssocRing T]

variable {s : Set R}

theorem InClosure.recOn {R} [Ring R] {s : Set R}
    {C : R → Prop} {x : R} (hx : x ∈ Subring.closure s) (h1 : C 1)
    (hneg1 : C (-1)) (hs : ∀ z ∈ s, ∀ n, C n → C (z * n)) (ha : ∀ {x y}, C x → C y → C (x + y)) :
    C x := by
  have h0 : C 0 := add_neg_cancel (1 : R) ▸ ha h1 hneg1
  rcases Subring.exists_list_of_mem_closure hx with ⟨L, HL, rfl⟩
  clear hx
  induction L with
  | nil => exact h0
  | cons hd tl ih => ?_
  rw [List.forall_mem_cons] at HL
  suffices C (List.prod hd) by
    rw [List.map_cons, List.sum_cons]
    exact ha this (ih HL.2)
  replace HL := HL.1
  clear ih tl
  rsuffices ⟨L, HL', HP | HP⟩ :
    ∃ L : List R, (∀ x ∈ L, x ∈ s) ∧ (List.prod hd = List.prod L ∨ List.prod hd = -List.prod L)
  · rw [HP]
    clear HP HL hd
    induction L with
    | nil => exact h1
    | cons hd tl ih =>
      rw [List.forall_mem_cons] at HL'
      rw [List.prod_cons]
      exact hs _ HL'.1 _ (ih HL'.2)
  · rw [HP]
    clear HP HL hd
    induction L with
    | nil => exact hneg1
    | cons hd tl ih =>
      rw [List.prod_cons, neg_mul_eq_mul_neg]
      rw [List.forall_mem_cons] at HL'
      exact hs _ HL'.1 _ (ih HL'.2)
  induction hd with
  | nil => exact ⟨[], List.forall_mem_nil _, Or.inl rfl⟩
  | cons hd tl ih => ?_
  rw [List.forall_mem_cons] at HL
  rcases ih HL.2 with ⟨L, HL', HP | HP⟩ <;> rcases HL.1 with hhd | hhd
  · exact
      ⟨hd::L, List.forall_mem_cons.2 ⟨hhd, HL'⟩,
        Or.inl <| by rw [List.prod_cons, List.prod_cons, HP]⟩
  · exact ⟨L, HL', Or.inr <| by rw [List.prod_cons, hhd, neg_one_mul, HP]⟩
  · exact
      ⟨hd::L, List.forall_mem_cons.2 ⟨hhd, HL'⟩,
        Or.inr <| by rw [List.prod_cons, List.prod_cons, HP, neg_mul_eq_mul_neg]⟩
  · exact ⟨L, HL', Or.inl <| by rw [List.prod_cons, hhd, HP, neg_one_mul, neg_neg]⟩

