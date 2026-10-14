/-
Copyright (c) 2026 LocalityLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LocalityLean contributors
-/
import LocalityLean.Approx.Lindblad
import LocalityLean.Qudit.Witness

/-!
# Witness: a nonzero commutator for an open system

The derivative of `t ↦ [e^{tL} a, b]` at `t = 0` is `[L a, b]` for any bounded operator `L`
(M3, Lemma 6.1, generalizing M2's lemma from the generator of a family to any bounded
operator). For the two-qubit Hamiltonian `H = σ^x_0 σ^x_1` with the dephasing jump
`K = σ^z_0` and `a = σ^z_0`, `b = σ^z_1`, the dissipator vanishes on `a`, so `L a = i[H, a]`
and the double commutator is the nonzero one of M2; hence `[e^{tL} a, b] ≠ 0` at some `t > 0`
(M3, Theorem 6.2).

## Main statements

* `LocalityLean.hasDerivAt_comm_exp`, `LocalityLean.Qudit.TwoQubit.exists_comm_exp_ne_zero`.
-/

noncomputable section

namespace LocalityLean

open NormedSpace LinearAQFT

variable {Λ : Type*} {A : Type*} [CStarAlgebra A]

/-- M3, Lemma 6.1: the derivative of `t ↦ [e^{tL} a, b]` at `t = 0` is `[L a, b]`, for any
bounded operator `L`. -/
theorem hasDerivAt_comm_exp (L : A →L[ℂ] A) (a b : A) :
    HasDerivAt (fun t : ℝ => comm (exp (t • L) a) b) (comm (L a) b) 0 := by
  have h := hasDerivAt_exp_smul_const L (0 : ℝ)
  have h1 := HasFDerivAt.comp_hasDerivAt (0 : ℝ)
    ((ContinuousLinearMap.apply ℂ A a).restrictScalars ℝ).hasFDerivAt h
  have h2 := HasFDerivAt.comp_hasDerivAt (0 : ℝ)
    ((LocalGenerators.commRight b).restrictScalars ℝ).hasFDerivAt h1
  simpa [LocalGenerators.commRight_apply, Function.comp_def] using h2

namespace Qudit.TwoQubit

open scoped Matrix.Norms.L2Operator

theorem obsA_mem_pair : obsA ∈ localAlgebra ({0, 1} : Set (Fin 2)) :=
  localAlgebra_mono (by simp) (isLocal_siteOp (0 : Fin 2) pauliZ)

theorem star_obsA : star obsA = obsA := by
  rw [obsA, star_siteOp]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauliZ, Matrix.star_apply]

/-- The two-qubit open system: the Hamiltonian `σ^x_0 σ^x_1` with the dephasing jump
`σ^z_0`, on the support `{0, 1}`. -/
def dephasingTerm : LindbladTerm (quditNet fun _ : Fin 2 => Fin 2) where
  supp := {0, 1}
  H := ham
  H_mem := by rw [Finset.coe_pair]; exact ham_mem
  H_selfAdjoint := ham_selfAdjoint
  m := 1
  K := fun _ => obsA
  K_mem := fun _ => by rw [Finset.coe_pair]; exact obsA_mem_pair

/-- The dissipator vanishes on `a = σ^z_0`: `L a = i[H, a]`. -/
theorem dephasingTerm_gen_obsA : dephasingTerm.gen obsA = Complex.I • comm ham obsA := by
  rw [LindbladTerm.gen_apply, derivation_apply]
  simp [dephasingTerm, LindbladTerm.jump_apply_self star_obsA]

/-- The single-site operator of the identity is the identity (a lemma about `siteOp`, placed
here until M2's module is next revised). -/
theorem siteOp_one (u : Fin 2) : siteOp u (1 : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
  ext s s'
  rw [siteOp_apply, Matrix.one_apply, Matrix.one_apply]
  by_cases h : s = s'
  · subst h
    simp [agreesOff_refl]
  · have key : ¬ (AgreesOff {u} s s' ∧ s u = s' u) := fun ⟨ha, hu⟩ => h (funext fun v => by
      by_cases hv : v = u
      · subst hv; exact hu
      · exact ha v (by simpa using hv))
    by_cases ha : AgreesOff {u} s s'
    · have hu : s u ≠ s' u := fun hu => key ⟨ha, hu⟩
      simp [ha, hu, h]
    · simp [ha, h]

theorem pauliZ_mul_pauliZ : pauliZ * pauliZ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauliZ]

theorem obsA_mul_obsA : obsA * obsA = 1 := by
  rw [obsA, siteOp_mul_same, pauliZ_mul_pauliZ, siteOp_one]

theorem obsA_mem_single : obsA ∈ localAlgebra ({0} : Set (Fin 2)) :=
  isLocal_siteOp (0 : Fin 2) pauliZ

/-- A pure dephasing term on the site `0`: no Hamiltonian part, the one jump `σ^z_0`. -/
def dephasingOnly : LindbladTerm (quditNet fun _ : Fin 2 => Fin 2) where
  supp := {0}
  H := 0
  H_mem := zero_mem _
  H_selfAdjoint := by rw [IsSelfAdjoint, star_zero]
  m := 1
  K := fun _ => obsA
  K_mem := fun _ => by rw [Finset.coe_singleton]; exact obsA_mem_single

theorem dephasingOnly_gen : dephasingOnly.gen = LindbladTerm.jump obsA := by
  change derivation (0 : QuditAlgebra fun _ : Fin 2 => Fin 2) +
    ∑ _j : Fin 1, LindbladTerm.jump obsA = LindbladTerm.jump obsA
  rw [derivation_zero, zero_add, Fin.sum_univ_one]

/-- M3, Proposition 5.4 as a Lindblad family: the one-term pure dephasing family, whose
contraction hypothesis is proved by the explicit formula. -/
def dephasingFamily : LindbladFamily Unit (quditNet fun _ : Fin 2 => Fin 2) where
  term := fun _ => dephasingOnly
  contraction := by
    intro J t ht
    rcases Finset.eq_empty_or_nonempty J with rfl | hJ
    · rw [Finset.sum_empty, smul_zero, exp_zero]
      exact (ContinuousLinearMap.norm_id_le :
        ‖(1 : QuditAlgebra (fun _ : Fin 2 => Fin 2) →L[ℂ] QuditAlgebra (fun _ : Fin 2 => Fin 2))‖
          ≤ 1)
    · have hJ' : J = Finset.univ := Finset.eq_univ_of_forall fun x => by
        obtain ⟨y, hy⟩ := hJ
        rwa [Subsingleton.elim x y]
      rw [hJ', Fintype.sum_unique, dephasingOnly_gen]
      exact LindbladTerm.norm_exp_smul_jump_le_one star_obsA obsA_mul_obsA ht

/-- M3, Theorem 6.2: a nonzero commutator at some positive time for the open system. -/
theorem exists_comm_exp_ne_zero :
    ∃ t : ℝ, 0 < t ∧ comm (exp (t • dephasingTerm.gen) obsA) obsB ≠ 0 := by
  refine exists_pos_ne_zero_of_hasDerivAt (hasDerivAt_comm_exp dephasingTerm.gen obsA obsB)
    ?_ ?_
  · simp [comm_obsA_obsB]
  · rw [dephasingTerm_gen_obsA]
    exact comm_comm_ne_zero

end Qudit.TwoQubit

end LocalityLean

end
