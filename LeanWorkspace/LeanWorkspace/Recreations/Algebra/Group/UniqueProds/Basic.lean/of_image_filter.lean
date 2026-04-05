import Mathlib

variable {G H : Type*} [Mul G] [Mul H] {A B : Finset G} {a0 b0 : G}

theorem of_image_filter [DecidableEq H]
    (f : G →ₙ* H) {A B : Finset G} {aG bG : G} {aH bH : H} (hae : f aG = aH) (hbe : f bG = bH)
    (huH : UniqueMul (A.image f) (B.image f) aH bH)
    (huG : UniqueMul {a ∈ A | f a = aH} {b ∈ B | f b = bH} aG bG) :
    UniqueMul A B aG bG := fun a b ha hb he ↦ by
  specialize huH (mem_image_of_mem _ ha) (mem_image_of_mem _ hb)
  rw [← map_mul, he, map_mul, hae, hbe] at huH
  refine huG ?_ ?_ he <;> rw [mem_filter]
  exacts [⟨ha, (huH rfl).1⟩, ⟨hb, (huH rfl).2⟩]

