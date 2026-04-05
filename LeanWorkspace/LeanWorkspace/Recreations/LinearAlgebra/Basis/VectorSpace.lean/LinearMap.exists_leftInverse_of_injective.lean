import Mathlib

variable {ι : Type*} {ι' : Type*} {K : Type*} {V : Type*} {V' : Type*}

variable [DivisionRing K] [AddCommGroup V] [AddCommGroup V'] [Module K V] [Module K V']

variable {v : ι → V} {s t : Set V} {x y z : V}

theorem LinearMap.exists_leftInverse_of_injective (f : V →ₗ[K] V') (hf_inj : LinearMap.ker f = ⊥) :
    ∃ g : V' →ₗ[K] V, g.comp f = LinearMap.id := by
  let B := Basis.ofVectorSpaceIndex K V
  let hB := Basis.ofVectorSpace K V
  have hB₀ : _ := hB.linearIndependent.linearIndepOn_id
  have : LinearIndepOn K _root_.id (f '' B) := by
    have h₁ : LinearIndepOn K _root_.id (f '' Set.range (Basis.ofVectorSpace K V)) :=
      LinearIndepOn.image (f := f) hB₀ (show Disjoint _ _ by simp [hf_inj])
    rwa [Basis.range_ofVectorSpace K V] at h₁
  let C := this.extend (subset_univ _)
  have BC := Module.Basis.subset_extend this (subset_univ _)
  let hC := Basis.extend this
  haveI Vinh : Inhabited V := ⟨0⟩
  refine ⟨(hC.constr ℕ : _ → _) (C.restrict (invFun f)), hB.ext fun b => ?_⟩
  rw [image_subset_iff] at BC
  have fb_eq : f b = hC ⟨f b, BC b.2⟩ := by
    change f b = Basis.extend this _
    simp_rw [Basis.extend_apply_self]
  dsimp
  rw [Basis.ofVectorSpace_apply_self, fb_eq, hC.constr_basis]
  exact leftInverse_invFun (LinearMap.ker_eq_bot.1 hf_inj) _

