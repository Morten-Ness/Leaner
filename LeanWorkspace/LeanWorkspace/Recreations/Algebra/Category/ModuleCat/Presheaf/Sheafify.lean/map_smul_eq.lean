import Mathlib

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}

variable {R₀ : Cᵒᵖ ⥤ RingCat.{u}} {R : Sheaf J RingCat.{u}} (α : R₀ ⟶ R.obj)
  [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]

variable {M₀ : PresheafOfModules.{v} R₀} {A : Sheaf J AddCommGrpCat.{v}}
  (φ : M₀.presheaf ⟶ A.obj)
  [Presheaf.IsLocallyInjective J φ] [Presheaf.IsLocallySurjective J φ]

variable {X Y : Cᵒᵖ} (π : X ⟶ Y) (r r' : R.obj.obj X) (m m' : A.obj.obj X)

theorem map_smul_eq {Y : Cᵒᵖ} (f : X ⟶ Y) (r₀ : R₀.obj Y) (hr₀ : α.app Y r₀ = R.obj.map f r)
    (m₀ : M₀.obj Y) (hm₀ : φ.app Y m₀ = A.obj.map f m) :
    A.obj.map f (PresheafOfModules.Sheafify.smul α φ r m) = φ.app Y (r₀ • m₀) := (PresheafOfModules.Sheafify.smulCandidate α φ r m).h f r₀ hr₀ m₀ hm₀

protected lemma one_smul : PresheafOfModules.Sheafify.smul α φ 1 m = m := by
  apply A.isSeparated _ _ (Presheaf.imageSieve_mem J φ m)
  rintro Y f ⟨m₀, hm₀⟩
  rw [← hm₀, map_smul_eq α φ 1 m f.op 1 (by simp) m₀ hm₀, one_smul]

