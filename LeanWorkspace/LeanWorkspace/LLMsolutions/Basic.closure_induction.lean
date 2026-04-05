import Mathlib

variable {K : Type u} {L : Type v} {M : Type w}

variable [DivisionRing K] [DivisionRing L] [DivisionRing M]

theorem closure_induction {s : Set K} {p : ∀ x ∈ Subfield.closure s, Prop}
    (mem : ∀ x hx, p x (Subfield.subset_closure hx))
    (one : p 1 (one_mem _)) (add : ∀ x y hx hy, p x hx → p y hy → p (x + y) (add_mem hx hy))
    (neg : ∀ x hx, p x hx → p (-x) (neg_mem hx)) (inv : ∀ x hx, p x hx → p x⁻¹ (inv_mem hx))
    (mul : ∀ x y hx hy, p x hx → p y hy → p (x * y) (mul_mem hx hy))
    {x} (h : x ∈ Subfield.closure s) : p x h := by
  let S : Subfield K :=
    { carrier := {x | ∃ hx : x ∈ Subfield.closure s, p x hx}
      zero_mem' := by
        have h1 : (1 : K) ∈ Subfield.closure s := one_mem _
        have hm1 : (-1 : K) ∈ Subfield.closure s := neg_mem h1
        have h0 : (0 : K) ∈ Subfield.closure s := by
          simpa using add_mem hm1 h1
        refine ⟨h0, ?_⟩
        have hsum : p ((-1 : K) + 1) (add_mem hm1 h1) :=
          add (-1) 1 hm1 h1 (neg 1 h1 one) one
        simpa using hsum
      add_mem' := by
        intro x y hx hy
        rcases hx with ⟨hxmem, hxp⟩
        rcases hy with ⟨hymem, hyp⟩
        exact ⟨add_mem hxmem hymem, add x y hxmem hymem hxp hyp⟩
      neg_mem' := by
        intro x hx
        rcases hx with ⟨hxmem, hxp⟩
        exact ⟨neg_mem hxmem, neg x hxmem hxp⟩
      one_mem' := ⟨one_mem _, one⟩
      mul_mem' := by
        intro x y hx hy
        rcases hx with ⟨hxmem, hxp⟩
        rcases hy with ⟨hymem, hyp⟩
        exact ⟨mul_mem hxmem hymem, mul x y hxmem hymem hxp hyp⟩
      inv_mem' := by
        intro x hx
        rcases hx with ⟨hxmem, hxp⟩
        exact ⟨inv_mem hxmem, inv x hxmem hxp⟩ }
  have hs : s ⊆ S := by
    intro x hx
    exact ⟨Subfield.subset_closure hx, mem x hx⟩
  have hclosure : Subfield.closure s ≤ S := Subfield.closure_le.2 hs
  exact (hclosure h).2
