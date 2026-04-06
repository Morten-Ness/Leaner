FAIL
import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {N : Type*} [Group N] (H : Subgroup G)

theorem Normal.map {H : Subgroup G} (h : H.Normal) (f : G →* N) (hf : Function.Surjective f) :
    (H.map f).Normal := by
  classical
  let e : G ⧸ H ≃* N ⧸ H.map f :=
    QuotientGroup.quotientMulEquivOfSurjective f hf (by
      intro x
      constructor
      · intro hx
        exact ⟨x, hx, rfl⟩
      · intro hx
        rcases hx with ⟨y, hy, hxy⟩
        rwa [← hxy] at hy)
  let φ : N →* N ⧸ H.map f := QuotientGroup.mk' (H.map f)
  have hker : φ.ker = H.map f := by
    ext x
    simp [φ]
  have hsurj : Function.Surjective φ := QuotientGroup.mk'_surjective (H.map f)
  rw [← hker]
  exact MonoidHom.normal_ker φ
