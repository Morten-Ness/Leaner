FAIL
import Mathlib

variable {G : Type*} [Group G]

variable {A : Type*} [AddGroup A]

theorem mem_normalizer_fintype {S : Set G} [Finite S] {x : G} (h : ∀ n, n ∈ S → x * n * x⁻¹ ∈ S) :
    x ∈ Subgroup.normalizer S := by
  change ∀ n, n ∈ S ↔ x * n * x⁻¹ ∈ S
  intro n
  constructor
  · intro hn
    exact h n hn
  · intro hn
    classical
    let f : S → S := fun s => ⟨x * s.1 * x⁻¹, h s.1 s.2⟩
    have hf_inj : Function.Injective f := by
      intro a b hab
      apply Subtype.ext
      have h1 : x⁻¹ * (x * a.1 * x⁻¹) * x = x⁻¹ * (x * b.1 * x⁻¹) * x := by
        simpa [hab]
      simpa [mul_assoc] using h1
    have hf_surj : Function.Surjective f := Finite.surjective_of_injective f hf_inj
    rcases hf_surj ⟨x * n * x⁻¹, hn⟩ with ⟨m, hm⟩
    have hmx : x⁻¹ * m.1 * x = n := by
      have h1 : x⁻¹ * f m.1 * x = x⁻¹ * (x * n * x⁻¹) * x := by
        simpa using congrArg (fun y : G => x⁻¹ * y * x) (Subtype.ext_iff.mp hm)
      simpa [f, mul_assoc] using h1
    exact hmx ▸ m.2
