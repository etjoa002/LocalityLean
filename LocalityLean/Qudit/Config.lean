/-
Copyright (c) 2026 LocalityLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LocalityLean contributors
-/
import LocalityLean.Core.Support
import LocalAlgebrasLean.Qudit.Config

/-!
# The qudit net (now in LocalAlgebrasLean)

The qudit net of M2 (Definition 2.3, Lemma 4.1, Propositions 4.2, Theorem 4.3) moved to the
foundation library LocalAlgebrasLean. Its names are exported here
under `LocalityLean.Qudit`, so that every statement of M2 and later milestones keeps its text; the
causality of the qudit net for this library's lattice index is stated below.
-/

noncomputable section

namespace LocalityLean.Qudit

open LinearAQFT
open scoped Matrix.Norms.L2Operator

export LocalAlgebrasLean.Qudit (
  Config AgreesOff agreesOff_refl AgreesOff.symm AgreesOff.trans AgreesOff.mono agreesOff_univ
  restrict restrict_apply glue glue_agreesOff restrict_glue glue_restrict eq_iff_restrict_eq
  mix mix_agreesOff_left restrict_mix eq_mix mix_agreesOff_right QuditAlgebra IsLocal
  IsLocal.add IsLocal.smul isLocal_zero IsLocal.star IsLocal.mono isLocal_one sum_glue
  IsLocal.mul mul_apply_eq_mix commute_of_disjoint embed embed_apply isLocal_embed
  isLocal_iff_exists_embed localAlgebra mem_localAlgebra embed_mem mem_localAlgebra_iff
  localAlgebra_mono localAlgebra_univ localAlgebra_isClosed quditNet quditNet_apply)

variable {Λ : Type*} {σ : Λ → Type*}
variable [Fintype Λ] [DecidableEq Λ] [∀ u, Fintype (σ u)] [∀ u, DecidableEq (σ u)]

/-- M2, Theorem 4.3: the qudit net is causal for the lattice index (local commutativity for the
region index of the sites, `LocalAlgebrasLean.Qudit.quditNet_isLocallyCommutative`). -/
theorem quditNet_isCausal : Net.IsCausal (latticeIndex Λ) (quditNet σ) :=
  LocalAlgebrasLean.Qudit.quditNet_isLocallyCommutative

end LocalityLean.Qudit

end
