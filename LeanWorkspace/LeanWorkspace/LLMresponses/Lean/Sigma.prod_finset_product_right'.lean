FAIL
import Mathlib

variable {ι κ α β γ : Type*}

variable {s s₁ s₂ : Finset α} {a : α} {f g : α → β}

variable [CommMonoid β]

theorem prod_finset_product_right' (r : Finset (α × γ)) (s : Finset γ) (t : γ → Finset α)
    (h : ∀ p : α × γ, p ∈ r ↔ p.2 ∈ s ∧ p.1 ∈ t p.2) {f : α → γ → β} :
    ∏ p ∈ r, f p.1 p.2 = ∏ c ∈ s, ∏ a ∈ t c, f a c := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      have hr : r = ∅ := by
        apply Finset.eq_empty_iff_forall_not_mem.2
        intro p hp
        have := (h p).1 hp
        simpa using this.1
      simp [hr]
  | @insert c s hc ih =>
      have hc_notin_r : ∀ a ∈ t c, (a, c) ∉ r.erase (. , .) := by
        intro a ha
        simp
      have hsplit : r = (Finset.image (fun a => (a, c)) (t c)) ∪
          (r.filter fun p => p.2 ≠ c) := by
        apply Finset.ext
        intro p
        constructor
        · intro hp
          by_cases hpc : p.2 = c
          · left
            rcases p with ⟨a, d⟩
            simp at hpc
            subst d
            have hp' := (h (a, c)).1 hp
            simp [hp'.2]
          · right
            simp [hp, hpc]
        · intro hp
          rcases Finset.mem_union.mp hp with hp | hp
          · rcases Finset.mem_image.mp hp with ⟨a, ha, rfl⟩
            exact (h (a, c)).2 ⟨by simp [hc], ha⟩
          · simp at hp
            exact hp.1
      have hfilter :
          ∀ p : α × γ, p ∈ r.filter (fun p => p.2 ≠ c) ↔ p.2 ∈ s ∧ p.1 ∈ t p.2 := by
        intro p
        constructor
        · intro hp
          simp at hp
          have hp' := (h p).1 hp.1
          rcases hp' with ⟨hp2, hp1⟩
          have : p.2 ∈ insert c s := hp2
          simp at this
          rcases this with rfl | hs
          · exact False.elim (hp.2 rfl)
          · exact ⟨hs, hp1⟩
        · intro hp
          have hp' : p ∈ r := (h p).2 ⟨by simp [hc, hp.1], hp.2⟩
          simp [hp', hp.1, hc]
      rw [hsplit, Finset.prod_union]
      · simp only [Finset.prod_image]
        · rw [ih hfilter]
          refine congrArg₂ (· * ·) ?_ rfl
          rw [Finset.prod_congr rfl]
          intro a ha
          rfl
        · intro a _ b _ hab
          exact Prod.mk.inj hab |>.1
      · refine Finset.disjoint_left.2 ?_
        intro p hp1 hp2
        rcases Finset.mem_image.mp hp1 with ⟨a, ha, hpa⟩
        subst hpa
        simp at hp2
        exact hp2.2 rfl
