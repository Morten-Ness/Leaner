FAIL
import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {N : Type*} [Group N]

theorem normal_iInf_normal {ι : Sort*} {a : ι → Subgroup G}
    (norm : ∀ i : ι, (a i).Normal) : (iInf a).Normal :=
by
  classical
  letI : ∀ i : ι, (a i).Normal := norm
  infer_instance
