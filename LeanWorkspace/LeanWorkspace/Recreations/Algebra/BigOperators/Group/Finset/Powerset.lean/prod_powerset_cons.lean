import Mathlib

variable {α β γ : Type*}

variable {s : Finset α} {a : α}

variable [CommMonoid β]

theorem prod_powerset_cons (ha : a ∉ s) (f : Finset α → β) :
    ∏ t ∈ (s.cons a ha).powerset, f t = (∏ t ∈ s.powerset, f t) *
      ∏ t ∈ s.powerset.attach, f (cons a t <| notMem_mono (mem_powerset.1 t.2) ha) := by
  classical
  simp_rw [cons_eq_insert]
  rw [Finset.prod_powerset_insert ha, prod_attach _ fun t ↦ f (insert a t)]

