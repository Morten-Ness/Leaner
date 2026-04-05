import Mathlib

variable {M : Type*}

variable [CommMonoid M] [Subsingleton Mˣ] {S : Set M}

theorem irreducible_mem_submonoidClosure_subset : {p ∈ Submonoid.closure S | Irreducible p} ⊆ S := by
  refine fun x hx ↦
      Submonoid.closure_induction (s := S) (motive := fun x _ ↦ (Irreducible x → x ∈ S))
      (fun _ hx _ ↦ hx) (by simp) (fun a b _ _ ha hb h ↦ ?_) hx.1 hx.2
  obtain rfl | rfl := h.eq_one_or_eq_one <;> simp_all

