import Mathlib

variable {ι κ M R : Type*} {s s₁ s₂ : Finset ι} {i : ι}

variable [CommSemiring R]

variable [DecidableEq ι]

set_option backward.isDefEq.respectTransparency false in
theorem prod_add (f g : ι → R) (s : Finset ι) :
    ∏ i ∈ s, (f i + g i) = ∑ t ∈ s.powerset, (∏ i ∈ t, f i) * ∏ i ∈ s \ t, g i := by
  classical
  calc
    ∏ i ∈ s, (f i + g i) =
        ∏ i ∈ s, ∑ p ∈ ({True, False} : Finset Prop), if p then f i else g i := by simp
    _ = ∑ p ∈ (s.pi fun _ => {True, False} : Finset (∀ a ∈ s, Prop)),
          ∏ a ∈ s.attach, if p a.1 a.2 then f a.1 else g a.1 := Finset.prod_sum _ _ _
    _ = ∑ t ∈ s.powerset, (∏ a ∈ t, f a) * ∏ a ∈ s \ t, g a :=
      sum_bij'
        (fun f _ ↦ {a ∈ s | ∃ h : a ∈ s, f a h})
        (fun t _ a _ => a ∈ t)
        (by simp)
        (by simp [Classical.em])
        (by simp_rw [mem_filter, funext_iff, eq_iff_iff, mem_pi, mem_insert]; tauto)
        (by simp_rw [Finset.ext_iff, @mem_filter _ _ (id _), mem_powerset]; tauto)
        (fun a _ ↦ by
          simp only [prod_ite, filter_attach', prod_map, Function.Embedding.coeFn_mk,
            Subtype.map_coe, id_eq, prod_attach]
          congr 2 with x
          simp only [mem_filter, mem_sdiff, not_and, not_exists, and_congr_right_iff]
          tauto)

