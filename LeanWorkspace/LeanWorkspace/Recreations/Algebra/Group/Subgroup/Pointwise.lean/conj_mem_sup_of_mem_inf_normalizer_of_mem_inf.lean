import Mathlib

variable {α G A S : Type*}

variable [Group G] [AddGroup A] {s : Set G}

theorem conj_mem_sup_of_mem_inf_normalizer_of_mem_inf
    {H K : Subgroup G} {s : G} (hs : s ∈ normalizer H ⊓ normalizer K) (g : G) (hg : g ∈ H ⊔ K) :
    s * g * s⁻¹ ∈ H ⊔ K := by
  simp only [mem_inf, mem_normalizer_iff] at hs
  rw [sup_eq_closure] at hg
  refine closure_induction ?_ ?_ ?_ ?_ hg
  · intro x hx
    obtain hl | hr := (mem_union x _ _).mpr hx
    · exact mem_sup_left (by rwa [← hs.1])
    · exact mem_sup_right (by rwa [← hs.2])
  · simp
  · intros x y hx hy hsx hsy
    rw [show s * (x * y) * s⁻¹ = (s * x * s⁻¹) * (s * y * s⁻¹) by simp]
    exact mul_mem hsx hsy
  · intros x hx hsx
    exact inv_mem_iff.mp (by simpa [← mul_assoc])

