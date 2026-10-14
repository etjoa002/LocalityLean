/-
Copyright (c) 2026 LocalityLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LocalityLean contributors
-/
import LocalityLean.Core.Reverse
import Mathlib.Analysis.CStarAlgebra.Exponential

/-!
# Hamiltonian families on a causal net

A finite family of self-adjoint local terms `Φ_i ∈ 𝒜(S_i)` gives the derivation generators
`L_i a = i [Φ_i, a]` with strengths `κ_i = ‖Φ_i‖`. They satisfy the three hypotheses of the
path-sum bound: (G1) is the homogeneity of the commutator seminorm, (G2) isotony, (G3) in both
time directions the unitarity of `e^{itH_J}` (M2, Section 3). The dynamics is computed to be the
conjugation `a ↦ U_t a U_t^*` with `U_t = exp(itH)`, from the exponential of commuting left and
right multiplications (M2, Proposition 3.2), and the role exchange
`‖[A(t), b]‖ = ‖[B(-t), a]‖` gives the second branch of the boundary refinement of
Nachtergaele-Sims-Young 2019, eq. (3.24) (M2, Theorem 3.5).

## Main definitions

* `LocalityLean.derivation`, `LocalityLean.Interaction`, `Interaction.toGenerators`,
  `Interaction.unitaryAt`.

## Main statements

* `LocalityLean.exp_mul_clm_add_flip_apply`, `norm_derivation_apply_le`,
  `derivation_apply_mem`, `exp_smul_derivation_apply_eq_conj`.
* `Interaction.toGenerators_negContractive`, `Interaction.evolve_eq_conj`,
  `Interaction.norm_comm_evolve_eq`, `Interaction.liebRobinson_walk_min`,
  `Interaction.liebRobinson_decay_min`.
-/

noncomputable section

namespace LocalityLean

open NormedSpace LinearAQFT

variable {Λ : Type*} {A : Type*} [CStarAlgebra A]

/-! ### The exponential of a multiplication (M2, Proposition 3.2) -/

section ExpMul

/-- Powers of the left multiplication. -/
theorem mul_clm_pow (x : A) (n : ℕ) :
    (ContinuousLinearMap.mul ℂ A x) ^ n = ContinuousLinearMap.mul ℂ A (x ^ n) := by
  induction n with
  | zero => ext a; simp
  | succ n ih =>
    ext a
    simp [pow_succ, ih, mul_assoc]

/-- The exponential of a left multiplication is the left multiplication by the exponential. -/
theorem exp_mul_clm (x : A) :
    exp (ContinuousLinearMap.mul ℂ A x) = ContinuousLinearMap.mul ℂ A (exp x) := by
  rw [exp_eq_tsum ℂ, exp_eq_tsum ℂ]
  simp_rw [mul_clm_pow]
  have hs : Summable fun n : ℕ => (n.factorial⁻¹ : ℂ) • x ^ n := expSeries_summable' x
  rw [(ContinuousLinearMap.mul ℂ A).map_tsum hs]
  simp only [map_smul]

/-- Powers of the right multiplication. -/
theorem mul_clm_flip_pow (y : A) (n : ℕ) :
    ((ContinuousLinearMap.mul ℂ A).flip y) ^ n = (ContinuousLinearMap.mul ℂ A).flip (y ^ n) := by
  induction n with
  | zero => ext a; simp
  | succ n ih =>
    ext a
    rw [pow_succ', ih]
    change (ContinuousLinearMap.mul ℂ A).flip y ((ContinuousLinearMap.mul ℂ A).flip (y ^ n) a)
      = (ContinuousLinearMap.mul ℂ A).flip (y ^ (n + 1)) a
    simp only [ContinuousLinearMap.flip_apply, ContinuousLinearMap.mul_apply', mul_assoc,
      pow_succ]

/-- The exponential of a right multiplication is the right multiplication by the exponential. -/
theorem exp_mul_clm_flip (y : A) :
    exp ((ContinuousLinearMap.mul ℂ A).flip y) = (ContinuousLinearMap.mul ℂ A).flip (exp y) := by
  rw [exp_eq_tsum ℂ, exp_eq_tsum ℂ]
  simp_rw [mul_clm_flip_pow]
  have hs : Summable fun n : ℕ => (n.factorial⁻¹ : ℂ) • y ^ n := expSeries_summable' y
  rw [(ContinuousLinearMap.mul ℂ A).flip.map_tsum hs]
  simp only [map_smul]

/-- Left and right multiplications commute. -/
theorem commute_mul_clm_flip (x y : A) :
    Commute (ContinuousLinearMap.mul ℂ A x) ((ContinuousLinearMap.mul ℂ A).flip y) := by
  ext a; simp [mul_assoc]

/-- M2, Proposition 3.2: `exp (m_x + m^y) a = e^x a e^y`. -/
theorem exp_mul_clm_add_flip_apply (x y a : A) :
    exp (ContinuousLinearMap.mul ℂ A x + (ContinuousLinearMap.mul ℂ A).flip y) a
      = exp x * a * exp y := by
  let _ : NormedAlgebra ℚ (A →L[ℂ] A) := NormedAlgebra.restrictScalars ℚ ℂ _
  rw [exp_add_of_commute (commute_mul_clm_flip x y), exp_mul_clm, exp_mul_clm_flip]
  simp [mul_assoc]

end ExpMul

/-! ### Time reversal for the matrix exponential (M2, Theorem 5.2 (i)) -/

open scoped Matrix.Norms.Operator in
set_option backward.isDefEq.respectTransparency false in
open Classical in
/-- M1b's finite-lattice form for every real `t`: for a negation-contractive family on a finite
site set, `‖[A(t), b]‖ ≤ 2‖a‖‖b‖ ([X ∩ Y ≠ ∅] + Σ_{y ∈ ∂Y, x ∈ X ∩ T} (e^{2|t|h} - 1)_{yx})`. -/
theorem LocalGenerators.liebRobinson_matrixExp_abs {ι : Type*} [Fintype ι]
    {𝒜 : Net (Set Λ) A} (G : LocalGenerators ι 𝒜) [Fintype Λ] [DecidableEq Λ]
    (hc : Net.IsCausal (latticeIndex Λ) 𝒜) (h : G.NegContractive) (X Y : Set Λ) {a b : A}
    (ha : a ∈ 𝒜 X) (hb : b ∈ 𝒜 Y) (t : ℝ) :
    ‖comm (G.evolve t a) b‖ ≤
      2 * ‖a‖ * ‖b‖ * ((if (X ∩ Y).Nonempty then 1 else 0) +
        ∑ y ∈ G.boundary Y, ∑ x ∈ G.regionSites X,
          (NormedSpace.exp ((2 * |t|) • G.toMatrix) y x - (1 : Matrix Λ Λ ℝ) y x)) := by
  rw [← G.tsum_walkTerm_eq X Y |t|]
  exact G.liebRobinson_walk_abs hc h X Y ha hb t

/-! ### Derivations (M2, Definition 2.1 and Proposition 3.1) -/

/-- The derivation `ad_x : a ↦ i [x, a]`, a bounded operator on the algebra. -/
def derivation (x : A) : A →L[ℂ] A :=
  Complex.I • (ContinuousLinearMap.mul ℂ A x - (ContinuousLinearMap.mul ℂ A).flip x)

theorem derivation_apply (x a : A) : derivation x a = Complex.I • comm x a := by
  simp [derivation, comm]

theorem derivation_zero : derivation (0 : A) = 0 := by
  ext a; simp [derivation_apply, comm]

theorem derivation_add (x y : A) : derivation (x + y) = derivation x + derivation y := by
  ext a; simp [derivation_apply, comm_add_left, smul_add]

theorem derivation_neg (x : A) : derivation (-x) = -derivation x := by
  ext a
  rw [neg_apply, derivation_apply, derivation_apply, ← smul_neg]
  congr 1
  simp only [comm, neg_mul, mul_neg]
  abel

theorem derivation_sum {ι : Type*} (s : Finset ι) (f : ι → A) :
    derivation (∑ i ∈ s, f i) = ∑ i ∈ s, derivation (f i) := by
  classical
  refine Finset.induction_on s (by simp [derivation_zero]) fun a s ha ih => ?_
  rw [Finset.sum_insert ha, Finset.sum_insert ha, derivation_add, ih]

/-- The operator bound `‖ad_x‖ ≤ 2‖x‖`. -/
theorem norm_derivation_le (x : A) : ‖derivation x‖ ≤ 2 * ‖x‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun a => by
    rw [derivation_apply, norm_smul, Complex.norm_I, one_mul]
    exact norm_comm_le x a

/-- M2, Proposition 3.1 (a), (G1) for a derivation: `‖ad_x c‖ ≤ ‖x‖ N_S(c)` for `x ∈ 𝒜(S)`. -/
theorem norm_derivation_apply_le (𝒜 : Net (Set Λ) A) {S : Set Λ} {x : A} (hx : x ∈ 𝒜 S)
    (c : A) : ‖derivation x c‖ ≤ ‖x‖ * commNorm 𝒜 S c := by
  rw [derivation_apply, norm_smul, Complex.norm_I, one_mul]
  rcases eq_or_ne x 0 with rfl | hx0
  · simp [comm]
  · have hpos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
    set b : A := ((‖x‖⁻¹ : ℝ) : ℂ) • x with hb_def
    have hb : b ∈ 𝒜 S := (𝒜 S).smul_mem hx _
    have hb1 : ‖b‖ ≤ 1 := by
      rw [hb_def, norm_smul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr hpos.le),
        inv_mul_cancel₀ hpos.ne']
    have hcb : comm c b = ((‖x‖⁻¹ : ℝ) : ℂ) • (-(comm x c)) := by
      rw [hb_def, comm_smul_right]
      congr 1
      simp only [comm]
      abel
    have hn : ‖comm c b‖ = ‖x‖⁻¹ * ‖comm x c‖ := by
      rw [hcb, norm_smul, norm_neg, Complex.norm_real,
        Real.norm_of_nonneg (inv_nonneg.mpr hpos.le)]
    have h1 := norm_comm_le_commNorm 𝒜 S (c := c) hb hb1
    rw [hn] at h1
    calc ‖comm x c‖ = ‖x‖ * (‖x‖⁻¹ * ‖comm x c‖) := by
          rw [← mul_assoc, mul_inv_cancel₀ hpos.ne', one_mul]
      _ ≤ ‖x‖ * commNorm 𝒜 S c := mul_le_mul_of_nonneg_left h1 hpos.le

/-- M2, Proposition 3.1 (b), (G2) for a derivation: `ad_x` maps `𝒜(Z)` into `𝒜(Z ∪ S)`. -/
theorem derivation_apply_mem (𝒜 : Net (Set Λ) A) {S Z : Set Λ} {x c : A} (hx : x ∈ 𝒜 S)
    (hc : c ∈ 𝒜 Z) : derivation x c ∈ 𝒜 (Z ∪ S) := by
  have hx' : x ∈ 𝒜 (Z ∪ S) := 𝒜.mono Set.subset_union_right hx
  have hc' : c ∈ 𝒜 (Z ∪ S) := 𝒜.mono Set.subset_union_left hc
  rw [derivation_apply, comm_def]
  exact (𝒜 (Z ∪ S)).smul_mem (sub_mem (mul_mem hx' hc') (mul_mem hc' hx')) _

/-! ### Unitary conjugation (M2, Proposition 3.3) -/

/-- `exp (i t H)` is unitary for `H` self-adjoint and real `t`. -/
theorem exp_I_smul_mem_unitary {H : A} (hH : IsSelfAdjoint H) (t : ℝ) :
    exp (Complex.I • ((t : ℂ) • H)) ∈ unitary A := by
  have ht' : IsSelfAdjoint (t : ℂ) := by
    rw [IsSelfAdjoint, Complex.star_def, Complex.conj_ofReal]
  exact (selfAdjoint.expUnitary ⟨(t : ℂ) • H, ht'.smul hH⟩).2

/-- `exp (i t H)^* = exp (-(i t H))`. -/
theorem star_exp_I_smul {H : A} (hH : IsSelfAdjoint H) (t : ℝ) :
    star (exp (Complex.I • ((t : ℂ) • H))) = exp (-(Complex.I • ((t : ℂ) • H))) := by
  rw [star_exp, star_smul, star_smul, Complex.star_def, Complex.conj_I, Complex.conj_ofReal,
    hH.star_eq, neg_smul]

/-- Conjugation by a unitary preserves the norm. -/
theorem norm_conj_eq [Nontrivial A] {U : A} (hU : U ∈ unitary A) (a : A) :
    ‖U * a * star U‖ = ‖a‖ := by
  rw [CStarRing.norm_mul_mem_unitary _ (Unitary.star_mem hU), CStarRing.norm_mem_unitary_mul _ hU]

theorem real_smul_I_smul (t : ℝ) (z : A) :
    t • (Complex.I • z) = Complex.I • ((t : ℂ) • z) := by
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ) t, smul_smul, smul_smul, mul_comm]
  exact rfl

/-- `t ad_H = m_{itH} + m^{-itH}`. -/
theorem smul_derivation_eq (H : A) (t : ℝ) :
    t • derivation H = ContinuousLinearMap.mul ℂ A (Complex.I • ((t : ℂ) • H)) +
      (ContinuousLinearMap.mul ℂ A).flip (-(Complex.I • ((t : ℂ) • H))) := by
  ext a
  simp only [smul_apply, add_apply, derivation_apply, comm, ContinuousLinearMap.mul_apply',
    ContinuousLinearMap.flip_apply, smul_sub, smul_mul_assoc, mul_smul_comm, mul_neg]
  rw [real_smul_I_smul, real_smul_I_smul, sub_eq_add_neg]

/-- `exp (t ad_H) a = e^{itH} a e^{-itH}`. -/
theorem exp_smul_derivation_apply (H : A) (t : ℝ) (a : A) :
    exp (t • derivation H) a =
      exp (Complex.I • ((t : ℂ) • H)) * a * exp (-(Complex.I • ((t : ℂ) • H))) := by
  rw [smul_derivation_eq, exp_mul_clm_add_flip_apply]

/-- M2, Proposition 3.3: `exp (t ad_H) a = U_t a U_t^*` for `H` self-adjoint. -/
theorem exp_smul_derivation_apply_eq_conj {H : A} (hH : IsSelfAdjoint H) (t : ℝ) (a : A) :
    exp (t • derivation H) a =
      exp (Complex.I • ((t : ℂ) • H)) * a * star (exp (Complex.I • ((t : ℂ) • H))) := by
  rw [exp_smul_derivation_apply, star_exp_I_smul hH]

theorem norm_exp_smul_derivation_apply [Nontrivial A] {H : A} (hH : IsSelfAdjoint H) (t : ℝ)
    (a : A) : ‖exp (t • derivation H) a‖ = ‖a‖ := by
  rw [exp_smul_derivation_apply_eq_conj hH, norm_conj_eq (exp_I_smul_mem_unitary hH t)]

/-- (G3) for a derivation of a self-adjoint element, in both time directions. -/
theorem norm_exp_smul_derivation_le_one [Nontrivial A] {H : A} (hH : IsSelfAdjoint H) (t : ℝ) :
    ‖exp (t • derivation H)‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun a => by
    rw [norm_exp_smul_derivation_apply hH, one_mul]

/-! ### Hamiltonian families (M2, Definition 2.1 and Theorem 3.4) -/

/-- A Hamiltonian family on the net: finite supports and self-adjoint local terms. -/
structure Interaction (ι : Type*) [Fintype ι] (𝒜 : Net (Set Λ) A) where
  /-- The support of the `i`-th term. -/
  supp : ι → Finset Λ
  /-- The `i`-th term. -/
  term : ι → A
  term_mem : ∀ i, term i ∈ 𝒜 (↑(supp i))
  term_selfAdjoint : ∀ i, IsSelfAdjoint (term i)

namespace Interaction

variable {ι : Type*} [Fintype ι] {𝒜 : Net (Set Λ) A} (Φ : Interaction ι 𝒜)

/-- The Hamiltonian of a sub-family, `H_J = Σ_{i ∈ J} Φ_i`. -/
def hamiltonian (J : Finset ι) : A := ∑ i ∈ J, Φ.term i

theorem hamiltonian_selfAdjoint (J : Finset ι) : IsSelfAdjoint (Φ.hamiltonian J) := by
  unfold hamiltonian
  rw [IsSelfAdjoint, star_sum]
  exact Finset.sum_congr rfl fun i _ => (Φ.term_selfAdjoint i).star_eq

theorem derivation_hamiltonian (J : Finset ι) :
    derivation (Φ.hamiltonian J) = ∑ i ∈ J, derivation (Φ.term i) :=
  derivation_sum J Φ.term

theorem norm_exp_subfamily_le_one [Nontrivial A] (J : Finset ι) (t : ℝ) :
    ‖exp (t • ∑ i ∈ J, derivation (Φ.term i))‖ ≤ 1 := by
  rw [← derivation_hamiltonian]
  exact norm_exp_smul_derivation_le_one (Φ.hamiltonian_selfAdjoint J) t

theorem norm_exp_neg_subfamily_le_one [Nontrivial A] (J : Finset ι) (t : ℝ) :
    ‖exp (t • ∑ i ∈ J, -derivation (Φ.term i))‖ ≤ 1 := by
  have : ∑ i ∈ J, -derivation (Φ.term i) = derivation (-(Φ.hamiltonian J)) := by
    rw [derivation_neg, derivation_hamiltonian, Finset.sum_neg_distrib]
  rw [this]
  exact norm_exp_smul_derivation_le_one (Φ.hamiltonian_selfAdjoint J).neg t

/-- M2, Theorem 3.4: a Hamiltonian family is a family of local generators with
`L_i = ad_{Φ_i}` and `κ_i = ‖Φ_i‖`. -/
def toGenerators [Nontrivial A] : LocalGenerators ι 𝒜 where
  supp := Φ.supp
  L i := derivation (Φ.term i)
  kappa i := ‖Φ.term i‖
  kappa_nonneg _ := norm_nonneg _
  local_in_arg i c := norm_derivation_apply_le 𝒜 (Φ.term_mem i) c
  maps_into i _ _ ha := derivation_apply_mem 𝒜 (Φ.term_mem i) ha
  contraction J t _ := Φ.norm_exp_subfamily_le_one J t

variable [Nontrivial A]

@[simp] theorem toGenerators_supp : Φ.toGenerators.supp = Φ.supp := rfl

@[simp] theorem toGenerators_L (i : ι) : Φ.toGenerators.L i = derivation (Φ.term i) := rfl

@[simp] theorem toGenerators_kappa (i : ι) : Φ.toGenerators.kappa i = ‖Φ.term i‖ := rfl

/-- M2, Theorem 3.4: the negated family is contractive. -/
theorem toGenerators_negContractive : Φ.toGenerators.NegContractive :=
  fun J t _ => Φ.norm_exp_neg_subfamily_le_one J t

theorem toGenerators_total : Φ.toGenerators.total = derivation (Φ.hamiltonian Finset.univ) := by
  rw [derivation_hamiltonian]; rfl

/-- The unitary `U_t = exp (i t H)` of the full Hamiltonian. -/
def unitaryAt (t : ℝ) : A := exp (Complex.I • ((t : ℂ) • Φ.hamiltonian Finset.univ))

omit [Nontrivial A] in
theorem unitaryAt_mem (t : ℝ) : Φ.unitaryAt t ∈ unitary A :=
  exp_I_smul_mem_unitary (Φ.hamiltonian_selfAdjoint _) t

omit [Nontrivial A] in
theorem star_unitaryAt (t : ℝ) : star (Φ.unitaryAt t) = Φ.unitaryAt (-t) := by
  unfold unitaryAt
  rw [star_exp_I_smul (Φ.hamiltonian_selfAdjoint _)]
  congr 1
  rw [Complex.ofReal_neg, neg_smul, smul_neg]

/-- M2, Theorem 3.4: the dynamics is the unitary conjugation `e^{tL} a = U_t a U_t^*`. -/
theorem evolve_eq_conj (t : ℝ) (a : A) :
    Φ.toGenerators.evolve t a = Φ.unitaryAt t * a * star (Φ.unitaryAt t) := by
  unfold LocalGenerators.evolve
  rw [toGenerators_total]
  exact exp_smul_derivation_apply_eq_conj (Φ.hamiltonian_selfAdjoint _) t a

/-! ### Role exchange (M2, Theorem 3.5) -/

omit [Nontrivial A] in
theorem comm_conj_eq {U : A} (hU : U ∈ unitary A) (a b : A) :
    comm (U * a * star U) b = U * comm a (star U * b * U) * star U := by
  have h1 : U * star U = 1 := Unitary.mul_star_self_of_mem hU
  simp only [comm, mul_sub, sub_mul, mul_assoc]
  rw [h1, mul_one, ← mul_assoc U (star U), h1, one_mul]

theorem norm_comm_conj_eq {U : A} (hU : U ∈ unitary A) (a b : A) :
    ‖comm (U * a * star U) b‖ = ‖comm a (star U * b * U)‖ := by
  rw [comm_conj_eq hU, norm_conj_eq hU]

omit [Nontrivial A] in
theorem norm_comm_comm (a b : A) : ‖comm a b‖ = ‖comm b a‖ := by
  rw [show comm a b = -comm b a by simp only [comm]; abel, norm_neg]

/-- M2, Theorem 3.5: `‖[A(t), b]‖ = ‖[B(-t), a]‖`. -/
theorem norm_comm_evolve_eq (t : ℝ) (a b : A) :
    ‖comm (Φ.toGenerators.evolve t a) b‖ = ‖comm (Φ.toGenerators.evolve (-t) b) a‖ := by
  rw [evolve_eq_conj, evolve_eq_conj, norm_comm_conj_eq (Φ.unitaryAt_mem t), norm_comm_comm,
    ← star_unitaryAt, star_star]

open Classical in
/-- M2, Theorem 3.5: the walk bound with the roles exchanged, walks from `∂X` to `Y ∩ T`. -/
theorem liebRobinson_walk_exchange (hc : Net.IsCausal (latticeIndex Λ) 𝒜) (X Y : Set Λ)
    {a b : A} (ha : a ∈ 𝒜 X) (hb : b ∈ 𝒜 Y) (t : ℝ) :
    ‖comm (Φ.toGenerators.evolve t a) b‖ ≤
      2 * ‖a‖ * ‖b‖ * ((if (X ∩ Y).Nonempty then 1 else 0) +
        ∑' k, Φ.toGenerators.walkTerm Y X |t| k) := by
  rw [Φ.norm_comm_evolve_eq]
  have h := Φ.toGenerators.liebRobinson_walk_abs hc Φ.toGenerators_negContractive Y X hb ha (-t)
  rw [abs_neg, Set.inter_comm Y X] at h
  refine h.trans (le_of_eq ?_)
  ring

open Classical in
/-- M2, Theorem 3.5: the smaller of the two walk bounds. -/
theorem liebRobinson_walk_min (hc : Net.IsCausal (latticeIndex Λ) 𝒜) (X Y : Set Λ)
    {a b : A} (ha : a ∈ 𝒜 X) (hb : b ∈ 𝒜 Y) (t : ℝ) :
    ‖comm (Φ.toGenerators.evolve t a) b‖ ≤
      2 * ‖a‖ * ‖b‖ * ((if (X ∩ Y).Nonempty then 1 else 0) +
        min (∑' k, Φ.toGenerators.walkTerm X Y |t| k)
          (∑' k, Φ.toGenerators.walkTerm Y X |t| k)) := by
  rcases le_total (∑' k, Φ.toGenerators.walkTerm X Y |t| k)
    (∑' k, Φ.toGenerators.walkTerm Y X |t| k) with h | h
  · rw [min_eq_left h]
    exact Φ.toGenerators.liebRobinson_walk_abs hc Φ.toGenerators_negContractive X Y ha hb t
  · rw [min_eq_right h]
    exact Φ.liebRobinson_walk_exchange hc X Y ha hb t

open Classical in
/-- The decay bound with the roles exchanged. -/
theorem liebRobinson_decay_exchange (hc : Net.IsCausal (latticeIndex Λ) 𝒜) (K : DecayKernel Λ)
    {N : ℝ} (hN : Φ.toGenerators.IsFBound K N) (X Y : Set Λ) {a b : A} (ha : a ∈ 𝒜 X)
    (hb : b ∈ 𝒜 Y) (t : ℝ) :
    ‖comm (Φ.toGenerators.evolve t a) b‖ ≤
      2 * ‖a‖ * ‖b‖ * ((if (X ∩ Y).Nonempty then 1 else 0) +
        (Real.exp (2 * N * K.CF * |t|) - 1) / K.CF * Φ.toGenerators.kernelSum K Y X) := by
  rw [Φ.norm_comm_evolve_eq]
  have h := Φ.toGenerators.liebRobinson_decay_abs hc Φ.toGenerators_negContractive K hN Y X hb ha
    (-t)
  rw [abs_neg, Set.inter_comm Y X] at h
  refine h.trans (le_of_eq ?_)
  ring

open Classical in
/-- M2, Theorem 3.5 for the decay form: the smaller of the two kernel sums. -/
theorem liebRobinson_decay_min (hc : Net.IsCausal (latticeIndex Λ) 𝒜) (K : DecayKernel Λ)
    {N : ℝ} (hN : Φ.toGenerators.IsFBound K N) (X Y : Set Λ) {a b : A} (ha : a ∈ 𝒜 X)
    (hb : b ∈ 𝒜 Y) (t : ℝ) :
    ‖comm (Φ.toGenerators.evolve t a) b‖ ≤
      2 * ‖a‖ * ‖b‖ * ((if (X ∩ Y).Nonempty then 1 else 0) +
        (Real.exp (2 * N * K.CF * |t|) - 1) / K.CF *
          min (Φ.toGenerators.kernelSum K X Y) (Φ.toGenerators.kernelSum K Y X)) := by
  rcases le_total (Φ.toGenerators.kernelSum K X Y) (Φ.toGenerators.kernelSum K Y X) with h | h
  · rw [min_eq_left h]
    exact Φ.toGenerators.liebRobinson_decay_abs hc Φ.toGenerators_negContractive K hN X Y ha hb t
  · rw [min_eq_right h]
    exact Φ.liebRobinson_decay_exchange hc K hN X Y ha hb t

end Interaction

end LocalityLean

end
