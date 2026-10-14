/-
Copyright (c) 2026 LocalityLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LocalityLean contributors
-/
import LocalityLean.Approx.Truncated
import LocalityLean.Core.Derivation

/-!
# The open-system instance: Lindblad terms as local generators

A Lindblad term on a region `S` is a self-adjoint `H ∈ 𝒜(S)` with finitely many jump operators
`K_j ∈ 𝒜(S)`; its generator in the Heisenberg picture is
`L_S a = i[H, a] + Σ_j (K_j^* a K_j - ½ (K_j^* K_j a + a K_j^* K_j))` (M3, Definition 2.4).
It is bounded by `2‖H‖ + 2 Σ_j ‖K_j‖²`, annihilates the local algebra of the complement of `S`
(causality), maps `𝒜(Z)` into `𝒜(Z ∪ S)` (isotony) and commutes with the adjoint (M3,
Proposition 5.1). On a net with local approximation this gives locality in the argument,
`L_S c = L_S (c - P_{Sᶜ} c)` and `‖L_S c‖ ≤ ‖L_S‖ N_S(c)` (M3, Theorem 5.2).

A Lindblad family carries the hypothesis `contraction`, that every sub-family generates a
contraction for `t ≥ 0` (G3; the norm-one property of unital completely positive maps is not in
Mathlib at the pin). With it the family is a family of local generators with strengths
`‖L_i‖`, or the explicit `2‖H_i‖ + 2 Σ_j ‖K_{ij}‖²`, and the path-sum bound, its closed forms
and the truncated dynamics hold for open systems (M3, Theorem 5.3). A single dephasing term,
`H = 0` and one self-adjoint jump with `K² = 1`, is contractive by the explicit formula
`e^{tL} a = ½(1 + e^{-2t}) a + ½(1 - e^{-2t}) K a K` (M3, Proposition 5.4).

## Main definitions

* `LocalityLean.LindbladTerm`, `LocalityLean.LindbladTerm.jump`,
  `LocalityLean.LindbladTerm.gen`, `LocalityLean.LindbladFamily`,
  `LocalityLean.LindbladFamily.toGenerators`.

## Main statements

* `LocalityLean.LindbladTerm.norm_gen_le`, `gen_apply_eq_zero_of_mem_compl`, `gen_apply_mem`,
  `star_gen_apply`, `gen_apply_eq_gen_sub`, `norm_gen_apply_le`;
* `LocalityLean.LindbladFamily.liebRobinson_walk`, `liebRobinson_cone`,
  `norm_sub_P_evolve_le`;
* `LocalityLean.LindbladTerm.exp_smul_jump_eq`, `norm_exp_smul_jump_le_one`.
-/

noncomputable section

namespace LocalityLean

open LinearAQFT NormedSpace

variable {Λ : Type*} {A : Type*} [CStarAlgebra A]

/-! ### Lindblad terms (M3, Definition 2.4) -/

/-- A Lindblad term: a support, a self-adjoint Hamiltonian part and finitely many jump
operators, all local to the support. -/
structure LindbladTerm (𝒜 : Net (Set Λ) A) where
  /-- The support. -/
  supp : Finset Λ
  /-- The Hamiltonian part. -/
  H : A
  H_mem : H ∈ 𝒜 ↑supp
  H_selfAdjoint : IsSelfAdjoint H
  /-- The number of jump operators. -/
  m : ℕ
  /-- The jump operators. -/
  K : Fin m → A
  K_mem : ∀ j, K j ∈ 𝒜 ↑supp

namespace LindbladTerm

/-- The dissipator of one jump operator, `a ↦ K^* a K - ½ (K^* K a + a K^* K)`. -/
def jump (K : A) : A →L[ℂ] A :=
  ContinuousLinearMap.mulLeftRight ℂ A (star K) K -
    (2 : ℂ)⁻¹ • ContinuousLinearMap.mul ℂ A (star K * K) -
    (2 : ℂ)⁻¹ • (ContinuousLinearMap.mul ℂ A).flip (star K * K)

theorem jump_apply (K a : A) :
    jump K a = star K * a * K - (2 : ℂ)⁻¹ • (star K * K * a) - (2 : ℂ)⁻¹ • (a * (star K * K)) := by
  simp [jump, ContinuousLinearMap.mulLeftRight_apply, ContinuousLinearMap.mul_apply',
    ContinuousLinearMap.flip_apply]

theorem norm_two_inv : ‖(2 : ℂ)⁻¹‖ = (2 : ℝ)⁻¹ := by
  rw [norm_inv]
  norm_num

theorem norm_jump_apply_le (K a : A) : ‖jump K a‖ ≤ 2 * ‖K‖ ^ 2 * ‖a‖ := by
  rw [jump_apply]
  have hKK : ‖star K * K‖ ≤ ‖K‖ ^ 2 := by
    calc ‖star K * K‖ ≤ ‖star K‖ * ‖K‖ := norm_mul_le _ _
      _ = ‖K‖ ^ 2 := by rw [norm_star, sq]
  have h1 : ‖star K * a * K‖ ≤ ‖K‖ ^ 2 * ‖a‖ := by
    calc ‖star K * a * K‖ ≤ ‖star K * a‖ * ‖K‖ := norm_mul_le _ _
      _ ≤ ‖star K‖ * ‖a‖ * ‖K‖ := by gcongr; exact norm_mul_le _ _
      _ = ‖K‖ ^ 2 * ‖a‖ := by rw [norm_star]; ring
  have h2 : ‖(2 : ℂ)⁻¹ • (star K * K * a)‖ ≤ (2 : ℝ)⁻¹ * (‖K‖ ^ 2 * ‖a‖) := by
    rw [norm_smul, norm_two_inv]
    gcongr
    calc ‖star K * K * a‖ ≤ ‖star K * K‖ * ‖a‖ := norm_mul_le _ _
      _ ≤ ‖K‖ ^ 2 * ‖a‖ := by gcongr
  have h3 : ‖(2 : ℂ)⁻¹ • (a * (star K * K))‖ ≤ (2 : ℝ)⁻¹ * (‖K‖ ^ 2 * ‖a‖) := by
    rw [norm_smul, norm_two_inv]
    gcongr
    calc ‖a * (star K * K)‖ ≤ ‖a‖ * ‖star K * K‖ := norm_mul_le _ _
      _ ≤ ‖a‖ * ‖K‖ ^ 2 := by gcongr
      _ = ‖K‖ ^ 2 * ‖a‖ := mul_comm _ _
  calc ‖star K * a * K - (2 : ℂ)⁻¹ • (star K * K * a) - (2 : ℂ)⁻¹ • (a * (star K * K))‖
      ≤ ‖star K * a * K - (2 : ℂ)⁻¹ • (star K * K * a)‖ +
          ‖(2 : ℂ)⁻¹ • (a * (star K * K))‖ := norm_sub_le _ _
    _ ≤ ‖star K * a * K‖ + ‖(2 : ℂ)⁻¹ • (star K * K * a)‖ +
          ‖(2 : ℂ)⁻¹ • (a * (star K * K))‖ := by gcongr; exact norm_sub_le _ _
    _ ≤ ‖K‖ ^ 2 * ‖a‖ + (2 : ℝ)⁻¹ * (‖K‖ ^ 2 * ‖a‖) + (2 : ℝ)⁻¹ * (‖K‖ ^ 2 * ‖a‖) := by
        gcongr
    _ = 2 * ‖K‖ ^ 2 * ‖a‖ := by ring

theorem norm_jump_le (K : A) : ‖jump K‖ ≤ 2 * ‖K‖ ^ 2 :=
  ContinuousLinearMap.opNorm_le_bound _ (by positivity) (norm_jump_apply_le K)

/-- The dissipator vanishes on an element commuting with `K` and `K^*`. -/
theorem jump_apply_eq_zero_of_commute {K c : A} (h1 : Commute c K) (h2 : Commute c (star K)) :
    jump K c = 0 := by
  rw [jump_apply]
  have e1 : star K * c * K = star K * K * c := by
    rw [mul_assoc, h1.eq, ← mul_assoc]
  have e2 : c * (star K * K) = star K * K * c := (h2.mul_right h1).eq
  rw [e1, e2, sub_sub, ← add_smul, show ((2 : ℂ)⁻¹ + (2 : ℂ)⁻¹) = 1 by norm_num, one_smul,
    sub_self]

/-- The dissipator of a self-adjoint jump vanishes on the jump itself. -/
theorem jump_apply_self {K : A} (hK : star K = K) : jump K K = 0 :=
  jump_apply_eq_zero_of_commute (Commute.refl K) (by rw [hK])

theorem jump_apply_mem (𝒜 : Net (Set Λ) A) {S Z : Set Λ} {K c : A} (hK : K ∈ 𝒜 S)
    (hc : c ∈ 𝒜 Z) : jump K c ∈ 𝒜 (Z ∪ S) := by
  have hK' : K ∈ 𝒜 (Z ∪ S) := 𝒜.mono Set.subset_union_right hK
  have hc' : c ∈ 𝒜 (Z ∪ S) := 𝒜.mono Set.subset_union_left hc
  have hKs : star K ∈ 𝒜 (Z ∪ S) := star_mem hK'
  rw [jump_apply]
  exact sub_mem (sub_mem (mul_mem (mul_mem hKs hc') hK')
    ((𝒜 (Z ∪ S)).smul_mem (mul_mem (mul_mem hKs hK') hc') _))
    ((𝒜 (Z ∪ S)).smul_mem (mul_mem hc' (mul_mem hKs hK')) _)

theorem star_jump_apply (K a : A) : star (jump K a) = jump K (star a) := by
  rw [jump_apply, jump_apply]
  simp only [star_sub, star_smul, star_mul, star_star, star_inv₀, star_ofNat, mul_assoc]
  abel

variable {𝒜 : Net (Set Λ) A} (T : LindbladTerm 𝒜)

/-- The generator of a Lindblad term, `L_S = ad_H + Σ_j jump K_j`. -/
def gen : A →L[ℂ] A := derivation T.H + ∑ j, jump (T.K j)

theorem gen_apply (a : A) : T.gen a = derivation T.H a + ∑ j, jump (T.K j) a := by
  simp [gen]

/-- M3, Proposition 5.1 (a): `‖L_S‖ ≤ 2‖H‖ + 2 Σ_j ‖K_j‖²`. -/
theorem norm_gen_le : ‖T.gen‖ ≤ 2 * ‖T.H‖ + 2 * ∑ j, ‖T.K j‖ ^ 2 := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun a => ?_
  rw [gen_apply]
  calc ‖derivation T.H a + ∑ j, jump (T.K j) a‖
      ≤ ‖derivation T.H a‖ + ‖∑ j, jump (T.K j) a‖ := norm_add_le _ _
    _ ≤ ‖derivation T.H a‖ + ∑ j, ‖jump (T.K j) a‖ := by gcongr; exact norm_sum_le _ _
    _ ≤ 2 * ‖T.H‖ * ‖a‖ + ∑ j, 2 * ‖T.K j‖ ^ 2 * ‖a‖ := by
        gcongr with j _
        · calc ‖derivation T.H a‖ ≤ ‖derivation T.H‖ * ‖a‖ := ContinuousLinearMap.le_opNorm _ _
            _ ≤ 2 * ‖T.H‖ * ‖a‖ := by gcongr; exact norm_derivation_le _
        · exact norm_jump_apply_le _ _
    _ = (2 * ‖T.H‖ + 2 * ∑ j, ‖T.K j‖ ^ 2) * ‖a‖ := by
        rw [add_mul, mul_assoc (2 : ℝ) (∑ j, ‖T.K j‖ ^ 2) ‖a‖, Finset.sum_mul, Finset.mul_sum]
        congr 1
        refine Finset.sum_congr rfl fun j _ => ?_
        ring

/-- M3, Proposition 5.1 (b): `L_S` annihilates the local algebra of the complement of `S`. -/
theorem gen_apply_eq_zero_of_mem_compl (hc : Net.IsCausal (latticeIndex Λ) 𝒜) {c : A}
    (hcS : c ∈ 𝒜 (↑T.supp : Set Λ)ᶜ) : T.gen c = 0 := by
  rw [gen_apply]
  have hH : derivation T.H c = 0 := by
    rw [derivation_apply, comm_eq_zero_of_commute
      (commute_of_isCausal_of_disjoint hc disjoint_compl_right T.H_mem hcS), smul_zero]
  have hK : ∀ j, jump (T.K j) c = 0 := fun j =>
    jump_apply_eq_zero_of_commute
      (commute_of_isCausal_of_disjoint hc disjoint_compl_left hcS (T.K_mem j))
      (commute_of_isCausal_of_disjoint hc disjoint_compl_left hcS (star_mem (T.K_mem j)))
  simp [hH, hK]

/-- M3, Proposition 5.1 (c), (G2): `L_S` maps `𝒜(Z)` into `𝒜(Z ∪ S)`. -/
theorem gen_apply_mem {Z : Set Λ} {c : A} (hc : c ∈ 𝒜 Z) :
    T.gen c ∈ 𝒜 (Z ∪ ↑T.supp) := by
  rw [gen_apply]
  exact add_mem (derivation_apply_mem 𝒜 T.H_mem hc)
    (sum_mem fun j _ => jump_apply_mem 𝒜 (T.K_mem j) hc)

/-- M3, Proposition 5.1 (d): `L_S` commutes with the adjoint. -/
theorem star_gen_apply (a : A) : star (T.gen a) = T.gen (star a) := by
  rw [gen_apply, gen_apply, star_add, star_sum]
  congr 1
  · rw [derivation_apply, derivation_apply, star_smul, Complex.star_def, Complex.conj_I,
      comm_def, comm_def, star_sub, star_mul, star_mul, T.H_selfAdjoint.star_eq, neg_smul,
      smul_sub, smul_sub, neg_sub]
  · exact Finset.sum_congr rfl fun j _ => star_jump_apply _ _

/-- M3, Theorem 5.2: `L_S c = L_S (c - P_{Sᶜ} c)` on a net with local approximation. -/
theorem gen_apply_eq_gen_sub (hc : Net.IsCausal (latticeIndex Λ) 𝒜) (Q : LocalApprox 𝒜)
    (c : A) : T.gen c = T.gen (c - Q.P (↑T.supp : Set Λ)ᶜ c) := by
  rw [map_sub, T.gen_apply_eq_zero_of_mem_compl hc (Q.P_mem _ c), sub_zero]

/-- M3, Theorem 5.2, (G1): `‖L_S c‖ ≤ ‖L_S‖ N_S(c)`. -/
theorem norm_gen_apply_le (hc : Net.IsCausal (latticeIndex Λ) 𝒜) (Q : LocalApprox 𝒜) (c : A) :
    ‖T.gen c‖ ≤ ‖T.gen‖ * commNorm 𝒜 ↑T.supp c := by
  rw [T.gen_apply_eq_gen_sub hc Q c]
  calc ‖T.gen (c - Q.P (↑T.supp : Set Λ)ᶜ c)‖
      ≤ ‖T.gen‖ * ‖c - Q.P (↑T.supp : Set Λ)ᶜ c‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ ‖T.gen‖ * commNorm 𝒜 (↑T.supp : Set Λ)ᶜᶜ c := by
        gcongr
        exact Q.norm_sub_P_le _ c
    _ = ‖T.gen‖ * commNorm 𝒜 ↑T.supp c := by rw [compl_compl]

/-- The explicit strength. -/
def strength : ℝ := 2 * ‖T.H‖ + 2 * ∑ j, ‖T.K j‖ ^ 2

theorem strength_nonneg : 0 ≤ T.strength := by
  unfold strength
  positivity

theorem norm_gen_apply_le_strength (hc : Net.IsCausal (latticeIndex Λ) 𝒜) (Q : LocalApprox 𝒜)
    (c : A) : ‖T.gen c‖ ≤ T.strength * commNorm 𝒜 ↑T.supp c :=
  (T.norm_gen_apply_le hc Q c).trans
    (mul_le_mul_of_nonneg_right T.norm_gen_le (commNorm_nonneg _ _ _))

/-! ### Locality in the argument by the direct route (no local approximation) -/

/-- `‖[c, x]‖ ≤ ‖x‖ N_S(c)` for `x ∈ 𝒜 S`. -/
theorem norm_comm_le_norm_mul_commNorm {S : Set Λ} {x : A} (hx : x ∈ 𝒜 S) (c : A) :
    ‖comm c x‖ ≤ ‖x‖ * commNorm 𝒜 S c := by
  have h := norm_derivation_apply_le 𝒜 hx c
  rw [derivation_apply, norm_smul, Complex.norm_I, one_mul, Interaction.norm_comm_comm] at h
  exact h

/-- The dissipator as commutators: `D_K c = ½ K^* [c, K] + ½ [K^*, c] K`. -/
theorem jump_apply_eq_comm (K c : A) :
    jump K c = (2 : ℂ)⁻¹ • (star K * comm c K) + (2 : ℂ)⁻¹ • (comm (star K) c * K) := by
  rw [jump_apply, comm_def, comm_def]
  simp only [mul_sub, sub_mul, smul_sub, mul_assoc]
  module

/-- The direct estimate: `‖D_K c‖ ≤ ‖K‖² N_S(c)` for `K ∈ 𝒜 S`. -/
theorem norm_jump_apply_le_commNorm {S : Set Λ} {K : A} (hK : K ∈ 𝒜 S) (c : A) :
    ‖jump K c‖ ≤ ‖K‖ ^ 2 * commNorm 𝒜 S c := by
  rw [jump_apply_eq_comm]
  have h1 : ‖comm c K‖ ≤ ‖K‖ * commNorm 𝒜 S c := norm_comm_le_norm_mul_commNorm hK c
  have h2 : ‖comm (star K) c‖ ≤ ‖K‖ * commNorm 𝒜 S c := by
    rw [Interaction.norm_comm_comm]
    have := norm_comm_le_norm_mul_commNorm (star_mem hK) c
    rwa [norm_star] at this
  have hN := commNorm_nonneg 𝒜 S c
  calc ‖(2 : ℂ)⁻¹ • (star K * comm c K) + (2 : ℂ)⁻¹ • (comm (star K) c * K)‖
      ≤ ‖(2 : ℂ)⁻¹ • (star K * comm c K)‖ + ‖(2 : ℂ)⁻¹ • (comm (star K) c * K)‖ :=
        norm_add_le _ _
    _ ≤ (2 : ℝ)⁻¹ * (‖K‖ * (‖K‖ * commNorm 𝒜 S c)) +
          (2 : ℝ)⁻¹ * (‖K‖ * commNorm 𝒜 S c * ‖K‖) := by
        rw [norm_smul, norm_smul, norm_two_inv]
        gcongr
        · calc ‖star K * comm c K‖ ≤ ‖star K‖ * ‖comm c K‖ := norm_mul_le _ _
            _ ≤ ‖K‖ * (‖K‖ * commNorm 𝒜 S c) := by rw [norm_star]; gcongr
        · calc ‖comm (star K) c * K‖ ≤ ‖comm (star K) c‖ * ‖K‖ := norm_mul_le _ _
            _ ≤ ‖K‖ * commNorm 𝒜 S c * ‖K‖ := by gcongr
    _ = ‖K‖ ^ 2 * commNorm 𝒜 S c := by ring

/-- The direct strength `‖H‖ + Σ_j ‖K_j‖²`, half of `strength`. -/
def strengthDirect : ℝ := ‖T.H‖ + ∑ j, ‖T.K j‖ ^ 2

theorem strengthDirect_nonneg : 0 ≤ T.strengthDirect := by
  unfold strengthDirect
  positivity

theorem strength_eq_two_mul : T.strength = 2 * T.strengthDirect := by
  unfold strength strengthDirect
  ring

/-- (G1) by the direct route, on any net: `‖L_S c‖ ≤ (‖H‖ + Σ_j ‖K_j‖²) N_S(c)`. -/
theorem norm_gen_apply_le_direct (c : A) :
    ‖T.gen c‖ ≤ T.strengthDirect * commNorm 𝒜 ↑T.supp c := by
  rw [gen_apply]
  calc ‖derivation T.H c + ∑ j, jump (T.K j) c‖
      ≤ ‖derivation T.H c‖ + ∑ j, ‖jump (T.K j) c‖ :=
        (norm_add_le _ _).trans (by gcongr; exact norm_sum_le _ _)
    _ ≤ ‖T.H‖ * commNorm 𝒜 ↑T.supp c + ∑ j, ‖T.K j‖ ^ 2 * commNorm 𝒜 ↑T.supp c := by
        gcongr with j _
        · exact norm_derivation_apply_le 𝒜 T.H_mem c
        · exact norm_jump_apply_le_commNorm (T.K_mem j) c
    _ = T.strengthDirect * commNorm 𝒜 ↑T.supp c := by
        rw [strengthDirect, add_mul, Finset.sum_mul]

end LindbladTerm

/-! ### Lindblad families (M3, Definition 2.4 and Theorem 5.3) -/

/-- A Lindblad family: finitely many Lindblad terms with the hypothesis (G3) that every
sub-family generates a contraction for `t ≥ 0`. -/
structure LindbladFamily (ι : Type*) [Fintype ι] (𝒜 : Net (Set Λ) A) where
  /-- The terms. -/
  term : ι → LindbladTerm 𝒜
  /-- (G3), the contraction hypothesis: the norm-one property of unital completely positive
  maps, taken as a hypothesis. -/
  contraction : ∀ (J : Finset ι) (t : ℝ), 0 ≤ t → ‖exp (t • ∑ i ∈ J, (term i).gen)‖ ≤ 1

namespace LindbladFamily

variable {ι : Type*} [Fintype ι] {𝒜 : Net (Set Λ) A} (F : LindbladFamily ι 𝒜)
  (hc : Net.IsCausal (latticeIndex Λ) 𝒜) (Q : LocalApprox 𝒜)

/-- M3, Theorem 5.3: a Lindblad family on a causal net with local approximation is a family of
local generators with strengths `‖L_i‖`. -/
def toGenerators : LocalGenerators ι 𝒜 where
  supp i := (F.term i).supp
  L i := (F.term i).gen
  kappa i := ‖(F.term i).gen‖
  kappa_nonneg _ := norm_nonneg _
  local_in_arg i c := (F.term i).norm_gen_apply_le hc Q c
  maps_into i _ _ ha := (F.term i).gen_apply_mem ha
  contraction := F.contraction

/-- M3, Theorem 5.3 with the explicit strengths `2‖H_i‖ + 2 Σ_j ‖K_{ij}‖²`. -/
def toGeneratorsExplicit : LocalGenerators ι 𝒜 where
  supp i := (F.term i).supp
  L i := (F.term i).gen
  kappa i := (F.term i).strength
  kappa_nonneg i := (F.term i).strength_nonneg
  local_in_arg i c := (F.term i).norm_gen_apply_le_strength hc Q c
  maps_into i _ _ ha := (F.term i).gen_apply_mem ha
  contraction := F.contraction

@[simp] theorem toGenerators_supp (i : ι) : (F.toGenerators hc Q).supp i = (F.term i).supp := rfl

@[simp] theorem toGenerators_L (i : ι) : (F.toGenerators hc Q).L i = (F.term i).gen := rfl

@[simp] theorem toGenerators_kappa (i : ι) :
    (F.toGenerators hc Q).kappa i = ‖(F.term i).gen‖ := rfl

theorem toGenerators_total : (F.toGenerators hc Q).total = ∑ i, (F.term i).gen := rfl

open Classical in
/-- M3, Theorem 5.3, the walk form of the path-sum bound for open systems. -/
theorem liebRobinson_walk (X Y : Set Λ) {a b : A} (ha : a ∈ 𝒜 X) (hb : b ∈ 𝒜 Y) {t : ℝ}
    (ht : 0 ≤ t) :
    ‖comm ((F.toGenerators hc Q).evolve t a) b‖ ≤
      2 * ‖a‖ * ‖b‖ * ((if (X ∩ Y).Nonempty then 1 else 0) +
        ∑' k, (F.toGenerators hc Q).walkTerm X Y t k) :=
  (F.toGenerators hc Q).liebRobinson_walk hc X Y ha hb ht

open Classical in
/-- M3, Theorem 5.3, the exponential light cone for open systems. -/
theorem liebRobinson_cone (B : (F.toGenerators hc Q).BoundedGeometry) (X Y : Set Λ) {r : ℕ}
    (hr : 1 ≤ r)
    (hd : ∀ y ∈ (F.toGenerators hc Q).boundary Y, ∀ x ∈ (F.toGenerators hc Q).regionSites X,
      ((r : ℝ) - 1) * B.rho < B.d y x)
    (μ : ℝ) {a b : A} (ha : a ∈ 𝒜 X) (hb : b ∈ 𝒜 Y) {t : ℝ} (ht : 0 ≤ t) :
    ‖comm ((F.toGenerators hc Q).evolve t a) b‖ ≤
      2 * ‖a‖ * ‖b‖ * ((if (X ∩ Y).Nonempty then 1 else 0) +
        ((F.toGenerators hc Q).boundary Y).card * (Real.exp (B.v * t) *
          (Real.exp (-μ * r) * (Real.exp (Real.exp μ * (B.v * t)) - 1)))) :=
  (F.toGenerators hc Q).liebRobinson_cone hc B X Y hr hd μ ha hb ht

/-- M3, Theorem 5.3, the truncated dynamics for open systems. -/
theorem norm_sub_P_evolve_le {X X' : Set Λ} (hXX' : X ⊆ X') {a : A} (ha : a ∈ 𝒜 X) {t : ℝ}
    (ht : 0 ≤ t) :
    ‖(F.toGenerators hc Q).evolve t a - Q.P X' ((F.toGenerators hc Q).evolve t a)‖ ≤
      2 * ‖a‖ * ∑' k, (F.toGenerators hc Q).walkTerm X X'ᶜ t k :=
  (F.toGenerators hc Q).norm_sub_P_evolve_le hc Q hXX' ha ht

/-- M3, Theorem 5.3 by the direct route: a Lindblad family on any net is a family of local
generators with the strengths `‖H_i‖ + Σ_j ‖K_{ij}‖²`; no local approximation is needed. -/
def toGeneratorsDirect : LocalGenerators ι 𝒜 where
  supp i := (F.term i).supp
  L i := (F.term i).gen
  kappa i := (F.term i).strengthDirect
  kappa_nonneg i := (F.term i).strengthDirect_nonneg
  local_in_arg i c := (F.term i).norm_gen_apply_le_direct c
  maps_into i _ _ ha := (F.term i).gen_apply_mem ha
  contraction := F.contraction

@[simp] theorem toGeneratorsDirect_kappa (i : ι) :
    F.toGeneratorsDirect.kappa i = (F.term i).strengthDirect := rfl

include hc in
open Classical in
/-- The walk form of the path-sum bound for open systems with the direct strengths. -/
theorem liebRobinson_walk_direct (X Y : Set Λ) {a b : A} (ha : a ∈ 𝒜 X) (hb : b ∈ 𝒜 Y) {t : ℝ}
    (ht : 0 ≤ t) :
    ‖comm (F.toGeneratorsDirect.evolve t a) b‖ ≤
      2 * ‖a‖ * ‖b‖ * ((if (X ∩ Y).Nonempty then 1 else 0) +
        ∑' k, F.toGeneratorsDirect.walkTerm X Y t k) :=
  F.toGeneratorsDirect.liebRobinson_walk hc X Y ha hb ht

end LindbladFamily

/-! ### A dephasing term is contractive (M3, Proposition 5.4) -/

namespace LindbladTerm

/-- For a self-adjoint jump with `K² = 1`, the dissipator is `a ↦ K a K - a`. -/
theorem jump_eq_of_sq_eq_one {K : A} (hK : star K = K) (hK2 : K * K = 1) :
    jump K = ContinuousLinearMap.mulLeftRight ℂ A K K - 1 := by
  ext a
  rw [jump_apply, hK, hK2, one_mul, mul_one, sub_sub, ← add_smul,
    show ((2 : ℂ)⁻¹ + (2 : ℂ)⁻¹) = 1 by norm_num, one_smul]
  simp [ContinuousLinearMap.mulLeftRight_apply]

/-- The conjugation `a ↦ K a K` is an involution. -/
theorem mulLeftRight_sq_eq_one {K : A} (hK2 : K * K = 1) :
    ContinuousLinearMap.mulLeftRight ℂ A K K * ContinuousLinearMap.mulLeftRight ℂ A K K = 1 := by
  ext a
  change K * (K * a * K) * K = a
  rw [show K * (K * a * K) * K = (K * K) * a * (K * K) by simp only [mul_assoc], hK2, one_mul,
    mul_one]

/-- `L² = -2 L` for the dephasing dissipator. -/
theorem jump_sq {K : A} (hK : star K = K) (hK2 : K * K = 1) :
    jump K * jump K = (-2 : ℝ) • jump K := by
  rw [jump_eq_of_sq_eq_one hK hK2, sub_mul, mul_sub, mul_sub, mulLeftRight_sq_eq_one hK2]
  simp only [one_mul, mul_one]
  rw [show ((-2 : ℝ) • (ContinuousLinearMap.mulLeftRight ℂ A K K - 1)) =
    -((ContinuousLinearMap.mulLeftRight ℂ A K K - 1) +
      (ContinuousLinearMap.mulLeftRight ℂ A K K - 1)) by rw [neg_smul, two_smul]]
  abel

theorem jump_pow_succ {K : A} (hK : star K = K) (hK2 : K * K = 1) (n : ℕ) :
    jump K ^ (n + 1) = ((-2 : ℝ) ^ n) • jump K := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih, smul_mul_assoc, jump_sq hK hK2, smul_smul, pow_succ]

/-- M3, Proposition 5.4, the explicit formula: `e^{tL} = 1 + ½(1 - e^{-2t}) L`. -/
theorem exp_smul_jump_eq {K : A} (hK : star K = K) (hK2 : K * K = 1) (t : ℝ) :
    exp (t • jump K) = 1 + ((1 - Real.exp (-2 * t)) / 2) • jump K := by
  have hsum := expSeries_summable' (𝕂 := ℂ) (t • jump K)
  rw [congrFun (exp_eq_tsum (𝕂 := ℂ)) (t • jump K), hsum.tsum_eq_zero_add]
  simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, inv_one, one_smul]
  congr 1
  have hterm : ∀ n : ℕ, (((n + 1).factorial : ℂ)⁻¹) • (t • jump K) ^ (n + 1) =
      ((-1 / 2 : ℝ) * ((-2 * t) ^ (n + 1) / ((n + 1).factorial : ℝ))) • jump K := by
    intro n
    rw [smul_pow, jump_pow_succ hK hK2, smul_smul,
      RCLike.real_smul_eq_coe_smul (K := ℂ) (t ^ (n + 1) * (-2) ^ n),
      RCLike.real_smul_eq_coe_smul (K := ℂ)
        (-1 / 2 * ((-2 * t) ^ (n + 1) / ((n + 1).factorial : ℝ))), smul_smul]
    congr 1
    have hf : ((n + 1).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    push_cast
    rw [mul_pow, pow_succ (-2 : ℂ)]
    field_simp
  simp only [hterm]
  have hreal : HasSum (fun n : ℕ => (-2 * t) ^ (n + 1) / ((n + 1).factorial : ℝ))
      (Real.exp (-2 * t) - 1) := by
    have h := ((summable_nat_add_iff 1).2 (Real.summable_pow_div_factorial (-2 * t))).hasSum
    rwa [tsum_pow_succ_div_factorial] at h
  rw [(((hreal.mul_left (-1 / 2 : ℝ))).smul_const (jump K)).tsum_eq]
  congr 1
  ring

/-- M3, Proposition 5.4: a dephasing term generates a contraction for `t ≥ 0`. -/
theorem norm_exp_smul_jump_le_one [Nontrivial A] {K : A} (hK : star K = K) (hK2 : K * K = 1)
    {t : ℝ} (ht : 0 ≤ t) : ‖exp (t • jump K)‖ ≤ 1 := by
  have hKu : K ∈ unitary A := Unitary.mem_iff.mpr ⟨by rw [hK, hK2], by rw [hK, hK2]⟩
  have hC : ‖ContinuousLinearMap.mulLeftRight ℂ A K K‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun a => by
      rw [ContinuousLinearMap.mulLeftRight_apply, one_mul]
      have := norm_conj_eq hKu a
      rw [hK] at this
      exact this.le
  have he : Real.exp (-2 * t) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    linarith
  have he0 : 0 < Real.exp (-2 * t) := Real.exp_pos _
  rw [exp_smul_jump_eq hK hK2, jump_eq_of_sq_eq_one hK hK2, smul_sub]
  have : (1 : A →L[ℂ] A) + (((1 - Real.exp (-2 * t)) / 2) • ContinuousLinearMap.mulLeftRight ℂ A K K
      - ((1 - Real.exp (-2 * t)) / 2) • (1 : A →L[ℂ] A)) =
      ((1 + Real.exp (-2 * t)) / 2) • (1 : A →L[ℂ] A) +
        ((1 - Real.exp (-2 * t)) / 2) • ContinuousLinearMap.mulLeftRight ℂ A K K := by
    rw [show ((1 + Real.exp (-2 * t)) / 2 : ℝ) = 1 - (1 - Real.exp (-2 * t)) / 2 by ring,
      sub_smul, one_smul]
    abel
  rw [this]
  calc ‖((1 + Real.exp (-2 * t)) / 2) • (1 : A →L[ℂ] A) +
        ((1 - Real.exp (-2 * t)) / 2) • ContinuousLinearMap.mulLeftRight ℂ A K K‖
      ≤ ‖((1 + Real.exp (-2 * t)) / 2) • (1 : A →L[ℂ] A)‖ +
        ‖((1 - Real.exp (-2 * t)) / 2) • ContinuousLinearMap.mulLeftRight ℂ A K K‖ :=
        norm_add_le _ _
    _ = (1 + Real.exp (-2 * t)) / 2 * ‖(1 : A →L[ℂ] A)‖ +
        (1 - Real.exp (-2 * t)) / 2 * ‖ContinuousLinearMap.mulLeftRight ℂ A K K‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by linarith),
          abs_of_nonneg (by linarith)]
    _ ≤ (1 + Real.exp (-2 * t)) / 2 * 1 + (1 - Real.exp (-2 * t)) / 2 * 1 :=
        add_le_add
          (mul_le_mul_of_nonneg_left
            (ContinuousLinearMap.norm_id_le : ‖(1 : A →L[ℂ] A)‖ ≤ 1) (by linarith))
          (mul_le_mul_of_nonneg_left hC (by linarith))
    _ = 1 := by ring

/-- M3, Proposition 5.4, pointwise: `e^{tD} a = ½(1 + e^{-2t}) a + ½(1 - e^{-2t}) K a K`. -/
theorem exp_smul_jump_apply {K : A} (hK : star K = K) (hK2 : K * K = 1) (t : ℝ) (a : A) :
    exp (t • jump K) a =
      ((1 + Real.exp (-2 * t)) / 2) • a + ((1 - Real.exp (-2 * t)) / 2) • (K * a * K) := by
  rw [exp_smul_jump_eq hK hK2, jump_eq_of_sq_eq_one hK hK2]
  change a + ((1 - Real.exp (-2 * t)) / 2) • (K * a * K - a) = _
  rw [smul_sub, show ((1 + Real.exp (-2 * t)) / 2 : ℝ) = 1 - (1 - Real.exp (-2 * t)) / 2 by ring,
    sub_smul, one_smul]
  abel

end LindbladTerm

end LocalityLean

end
