FAIL
import Mathlib

variable {R k V1 P1 V2 P2 V3 P3 : Type*}

variable [Ring k] [AddCommGroup V1] [AddTorsor V1 P1] [AddCommGroup V2] [AddTorsor V2 P2]

variable [AddCommGroup V3] [AddTorsor V3 P3] [Module k V1] [Module k V2] [Module k V3]

variable {ι : Type*} {φv φp : ι → Type*} [(i : ι) → AddCommGroup (φv i)]
  [(i : ι) → Module k (φv i)] [(i : ι) → AddTorsor (φv i) (φp i)]

variable (fp : (i : ι) → (P1 →ᵃ[k] φp i)) (fv : (i : ι) → (P1 →ᵃ[k] φv i))
  (f' : ι → P1 →ᵃ[k] P2)

variable [Finite ι] [DecidableEq ι] {f g : ((i : ι) → φv i) →ᵃ[k] P2}

theorem pi_ext_zero (h : ∀ i x, f (Pi.single i x) = g (Pi.single i x)) (h₂ : f 0 = g 0) :
    f = g := by
  letI : Fintype ι := Fintype.ofFinite ι
  have hlin : f.linear = g.linear := by
    ext x i
    have hs : Pi.single i x = x • (Pi.single i (1 : k)) := by
      ext j
      by_cases hij : j = i
      · subst hij
        simp
      · simp [Pi.single, hij]
    rw [hs, LinearMap.map_smul]
    rw [hs, LinearMap.map_smul]
    have h1 := h i (1 : k)
    simpa using vsub_eq_sub (f (Pi.single i (1 : k))) (g (Pi.single i (1 : k))) ▸ h1
  ext x
  rw [← AffineMap.linear_eq (f := f) (g := g) h₂]
  simp [hlin]
