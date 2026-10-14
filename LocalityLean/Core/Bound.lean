/-
Copyright (c) 2026 LocalityLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LocalityLean contributors
-/
import LocalityLean.Core.Duhamel
import LocalityLean.Core.Path
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.Algebra.Order.Floor

/-!
# The master lemma

The probe-side Duhamel recursion and the path series (M1a, Propositions 3.5-3.7, Theorems 3.8,
3.10 and 3.11). Let `G` be a family of local generators on a net `𝒜` that is causal for the
lattice index, `a ∈ 𝒜 X`, `b ∈ 𝒜 Y`, `t ≥ 0`, and `A(t) = e^{tL} a`. Then

`‖[A(t), b]‖ ≤ 2 ‖a‖ ‖b‖ ([X ∩ Y ≠ ∅] + Σ_{k ≥ 1} (2t)^k / k! · P_k(Y, X))`,

with `P_k` the weighted count of first-contact paths (`pathSumRec`). The proof: Duhamel's
identity with the terms crossing `Y` (meeting `Y` and its complement) as the perturbation, the
terms inside `Y` annihilating `𝒜 Yᶜ` by (G1) and causality; the free term vanishes by support
closure and causality; the integrand is bounded by (G3) and (G1), which resets the probe to a
single support; an induction with an explicit remainder `2 (2tK)^{n+1}/(n+1)!` gives the
truncated series, and the limit gives the series.

## Main statements

* `LocalityLean.LocalGenerators.apply_eq_zero_of_subset` (Proposition 3.5, annihilation).
* `LocalityLean.LocalGenerators.exp_subfamily_apply_mem`, `exp_compl_crosses_apply_mem`
  (Proposition 3.6).
* `LocalityLean.LocalGenerators.comm_exp_compl_eq_zero` (Proposition 3.7).
* `LocalityLean.LocalGenerators.norm_comm_reset_le` (Proposition 3.8).
* `LocalityLean.LocalGenerators.norm_comm_evolve_le_of_majorant` (Theorem 3.9 in the form the
  induction uses: one Duhamel step with a continuous majorant of the reset commutators).
* `LocalityLean.LocalGenerators.norm_comm_evolve_le_truncBound` (Theorem 3.11).
* `LocalityLean.LocalGenerators.liebRobinson_path`, `liebRobinson`, `commBound_le`
  (Theorem 3.12, the three forms).
-/

noncomputable section

namespace LocalityLean

open LinearAQFT NormedSpace intervalIntegral Finset

variable {Λ : Type*} {A : Type*} [CStarAlgebra A]
variable {ι : Type*} [Fintype ι] {𝒜 : Net (Set Λ) A} (G : LocalGenerators ι 𝒜)

namespace LocalGenerators

/-! ### The restricted dynamics preserves the complement of the probe's region -/

/-- M1a, Proposition 3.6 (first part): the sub-family generator preserves `𝒜 W` when every
support of the sub-family lies in `W`. -/
theorem subfamily_apply_mem {J : Finset ι} {W : Set Λ} (hJ : ∀ i ∈ J, (G.supp i : Set Λ) ⊆ W)
    {c : A} (hc : c ∈ 𝒜 W) : G.subfamily J c ∈ 𝒜 W := by
  unfold subfamily
  rw [_root_.sum_apply]
  refine sum_mem fun i hi => ?_
  have h := G.maps_into i W c hc
  rwa [Set.union_eq_self_of_subset_right (hJ i hi)] at h

/-- M1a, Proposition 3.6 (second part): the restricted dynamics preserves `𝒜 W`. -/
theorem exp_subfamily_apply_mem {J : Finset ι} {W : Set Λ}
    (hJ : ∀ i ∈ J, (G.supp i : Set Λ) ⊆ W) (t : ℝ) {c : A} (hc : c ∈ 𝒜 W) :
    exp (t • G.subfamily J) c ∈ 𝒜 W :=
  exp_apply_mem_of_maps_into (G.subfamily J) (𝒜 W).toSubalgebra.toSubmodule (𝒜.isClosed W)
    (fun _ ha => G.subfamily_apply_mem hJ ha) t c hc

/-- A term whose support lies inside the probe's region annihilates the algebra of the
complement: for `c ∈ 𝒜 Yᶜ` the commutator seminorm `N_{S_i}(c)` vanishes by causality, and
(G1) gives `L_i c = 0`. -/
theorem apply_eq_zero_of_subset (hc : Net.IsCausal (latticeIndex Λ) 𝒜) {Y : Set Λ} {i : ι}
    (hi : (G.supp i : Set Λ) ⊆ Y) {c : A} (hcY : c ∈ 𝒜 Yᶜ) : G.L i c = 0 := by
  have h0 : commNorm 𝒜 (G.supp i) c = 0 :=
    commNorm_eq_zero_of_commute 𝒜 _ fun b hb =>
      commute_of_isCausal_of_disjoint hc disjoint_compl_left hcY (𝒜.mono hi hb)
  have h := G.local_in_arg i c
  rw [h0, mul_zero] at h
  exact norm_le_zero_iff.mp h

/-- The terms not crossing `Y` (disjoint from `Y` or inside `Y`) preserve `𝒜 Yᶜ`. -/
theorem subfamily_compl_crosses_apply_mem [DecidableEq ι] (hc : Net.IsCausal (latticeIndex Λ) 𝒜)
    (Y : Set Λ) {c : A} (hcY : c ∈ 𝒜 Yᶜ) : G.subfamily (G.crosses Y)ᶜ c ∈ 𝒜 Yᶜ := by
  unfold subfamily
  rw [_root_.sum_apply]
  refine sum_mem fun i hi => ?_
  rcases G.disjoint_or_subset_of_not_mem_crosses (Finset.mem_compl.mp hi) with h | h
  · have hm := G.maps_into i Yᶜ c hcY
    rwa [Set.union_eq_self_of_subset_right (Set.subset_compl_iff_disjoint_right.mpr h)] at hm
  · rw [G.apply_eq_zero_of_subset hc h hcY]
    exact zero_mem _

/-- The dynamics with the terms crossing `Y` switched off preserves `𝒜 Yᶜ`. -/
theorem exp_compl_crosses_apply_mem [DecidableEq ι] (hc : Net.IsCausal (latticeIndex Λ) 𝒜)
    (Y : Set Λ) (t : ℝ) {c : A} (hcY : c ∈ 𝒜 Yᶜ) :
    exp (t • G.subfamily (G.crosses Y)ᶜ) c ∈ 𝒜 Yᶜ :=
  exp_apply_mem_of_maps_into (G.subfamily (G.crosses Y)ᶜ) (𝒜 Yᶜ).toSubalgebra.toSubmodule
    (𝒜.isClosed Yᶜ) (fun _ ha => G.subfamily_compl_crosses_apply_mem hc Y ha) t c hcY

/-- M1a, Proposition 3.7: the first term of Duhamel's identity vanishes for disjoint regions. -/
theorem comm_exp_compl_eq_zero [DecidableEq ι] (hc : Net.IsCausal (latticeIndex Λ) 𝒜)
    {X Y : Set Λ} (hXY : Disjoint X Y) {a b : A} (ha : a ∈ 𝒜 X) (hb : b ∈ 𝒜 Y) (t : ℝ) :
    comm (exp (t • G.subfamily (G.crosses Y)ᶜ) a) b = 0 := by
  have ha' : a ∈ 𝒜 Yᶜ := 𝒜.mono (Set.subset_compl_iff_disjoint_right.mpr hXY) ha
  exact comm_eq_zero_of_commute (commute_of_isCausal_of_disjoint hc disjoint_compl_left
    (G.exp_compl_crosses_apply_mem hc Y t ha') hb)

/-! ### The reset step -/

/-- M1a, Proposition 3.8: the reset step. For `s ≤ t` and a unit `b`,
`‖[e^{(t-s)L'} (L^{∂Y} c), b]‖ ≤ 2 Σ_{i ∈ I^{∂Y}} κ_i N_{S_i}(c)`. -/
theorem norm_comm_reset_le [DecidableEq ι] (Y : Set Λ) {t s : ℝ} (hs : s ≤ t) (c b : A)
    (hb1 : ‖b‖ ≤ 1) :
    ‖comm (exp ((t - s) • G.subfamily (G.crosses Y)ᶜ) (G.subfamily (G.crosses Y) c)) b‖ ≤
      2 * ∑ i ∈ G.crosses Y, G.kappa i * commNorm 𝒜 (G.supp i) c := by
  have h1 := norm_comm_le
    (exp ((t - s) • G.subfamily (G.crosses Y)ᶜ) (G.subfamily (G.crosses Y) c)) b
  have h2 := (exp ((t - s) • G.subfamily (G.crosses Y)ᶜ)).le_opNorm (G.subfamily (G.crosses Y) c)
  have h3 := G.norm_exp_subfamily_le (G.crosses Y)ᶜ (sub_nonneg.mpr hs)
  have h4 := G.norm_subfamily_apply_le (G.crosses Y) c
  have h5 : 0 ≤ ‖G.subfamily (G.crosses Y) c‖ := norm_nonneg _
  have h6 : 0 ≤ ‖exp ((t - s) • G.subfamily (G.crosses Y)ᶜ) (G.subfamily (G.crosses Y) c)‖ :=
    norm_nonneg _
  calc _ ≤ 2 * ‖exp ((t - s) • G.subfamily (G.crosses Y)ᶜ) (G.subfamily (G.crosses Y) c)‖ * ‖b‖ :=
        h1
    _ ≤ 2 * ‖exp ((t - s) • G.subfamily (G.crosses Y)ᶜ) (G.subfamily (G.crosses Y) c)‖ * 1 := by
        gcongr
    _ ≤ 2 * (1 * ‖G.subfamily (G.crosses Y) c‖) * 1 := by
        gcongr
        exact h2.trans (mul_le_mul_of_nonneg_right h3 h5)
    _ ≤ 2 * (1 * ∑ i ∈ G.crosses Y, G.kappa i * commNorm 𝒜 (G.supp i) c) * 1 := by gcongr
    _ = 2 * ∑ i ∈ G.crosses Y, G.kappa i * commNorm 𝒜 (G.supp i) c := by ring

/-! ### One Duhamel step -/

/-- The commutator with `b` as a bounded linear map of the first argument. -/
def commRight (b : A) : A →L[ℂ] A :=
  (ContinuousLinearMap.mul ℂ A).flip b - ContinuousLinearMap.mul ℂ A b

theorem commRight_apply (b c : A) : commRight b c = comm c b := by
  simp [commRight, comm]

/-- The map `T ↦ [T a, b]` as a bounded linear map of `T`. -/
def commEval (a b : A) : (A →L[ℂ] A) →L[ℂ] A :=
  (commRight b).comp (ContinuousLinearMap.apply ℂ A a)

theorem commEval_apply (a b : A) (T : A →L[ℂ] A) : commEval a b T = comm (T a) b := by
  simp [commEval, commRight_apply]

/-- The Duhamel integrand `s ↦ e^{(t-s)P} Q e^{s(P+Q)}` is continuous. -/
theorem continuous_duhamel_integrand (P Q : A →L[ℂ] A) (t : ℝ) :
    Continuous fun s : ℝ => exp ((t - s) • P) * Q * exp (s • (P + Q)) :=
  ((continuous_exp_sub_smul P t).mul continuous_const).mul (continuous_exp_smul (P + Q))

/-- The evolution as the exponential of `L' + L^{∂Y}`. -/
theorem evolve_eq_exp_add [DecidableEq ι] (Y : Set Λ) (t : ℝ) :
    G.evolve t = exp (t • (G.subfamily (G.crosses Y)ᶜ + G.subfamily (G.crosses Y))) := by
  unfold evolve
  rw [G.total_eq_crosses_add_compl Y, add_comm]

/-- M1a, Theorem 3.9 in the form the induction uses: one Duhamel step. If, for every term `i`
crossing `Y`, the continuous function `g i` bounds the commutator seminorm `N_{S_i}(A(s))` on
`[0, t]`, then `‖[A(t), b]‖ ≤ 2 Σ_{i ∈ I^{∂Y}} κ_i ∫_0^t g i`. Regions disjoint, `b` unit. -/
theorem norm_comm_evolve_le_of_majorant (hc : Net.IsCausal (latticeIndex Λ) 𝒜) {X Y : Set Λ}
    (hXY : Disjoint X Y) {a b : A} (ha : a ∈ 𝒜 X) (hb : b ∈ 𝒜 Y) (hb1 : ‖b‖ ≤ 1) {t : ℝ}
    (ht : 0 ≤ t) (g : ι → ℝ → ℝ) (hg : ∀ i ∈ G.crosses Y, Continuous (g i))
    (hmaj : ∀ i ∈ G.crosses Y, ∀ s ∈ Set.Icc 0 t, commNorm 𝒜 (G.supp i) (G.evolve s a) ≤ g i s) :
    ‖comm (G.evolve t a) b‖ ≤ 2 * ∑ i ∈ G.crosses Y, G.kappa i * ∫ s in (0 : ℝ)..t, g i s := by
  classical
  set P := G.subfamily (G.crosses Y)ᶜ with hP
  set Q := G.subfamily (G.crosses Y) with hQ
  have hdu := duhamel P Q t
  have hev : G.evolve t = exp (t • (P + Q)) := G.evolve_eq_exp_add Y t
  have hev' : ∀ s, G.evolve s = exp (s • (P + Q)) := fun s => G.evolve_eq_exp_add Y s
  have hcont := continuous_duhamel_integrand P Q t
  have hint : IntervalIntegrable (fun s : ℝ => exp ((t - s) • P) * Q * exp (s • (P + Q)))
      MeasureTheory.volume 0 t := hcont.intervalIntegrable 0 t
  -- the commutator of Duhamel's identity applied to `a`
  have hsplit : comm (G.evolve t a) b =
      comm (exp (t • P) a) b +
        ∫ s in (0 : ℝ)..t, comm ((exp ((t - s) • P) * Q * exp (s • (P + Q))) a) b := by
    rw [hev, hdu, _root_.add_apply, comm_add_left]
    congr 1
    rw [← commEval_apply, ← (commEval a b).intervalIntegral_comp_comm hint]
    simp only [commEval_apply]
  have hfirst : comm (exp (t • P) a) b = 0 := G.comm_exp_compl_eq_zero hc hXY ha hb t
  rw [hsplit, hfirst, zero_add]
  -- the pointwise bound on `[0, t]`
  have hbound : ∀ s ∈ Set.Ioc (0 : ℝ) t,
      ‖comm ((exp ((t - s) • P) * Q * exp (s • (P + Q))) a) b‖ ≤
        2 * ∑ i ∈ G.crosses Y, G.kappa i * g i s := by
    intro s hs
    have hs' : s ∈ Set.Icc 0 t := ⟨hs.1.le, hs.2⟩
    change ‖comm (exp ((t - s) • P) (Q (exp (s • (P + Q)) a))) b‖ ≤ _
    rw [← hev' s]
    refine (G.norm_comm_reset_le Y hs.2 (G.evolve s a) b hb1).trans ?_
    gcongr with i hi
    · exact G.kappa_nonneg i
    · exact hmaj i hi s hs'
  have hgint : IntervalIntegrable (fun s => 2 * ∑ i ∈ G.crosses Y, G.kappa i * g i s)
      MeasureTheory.volume 0 t :=
    (continuous_const.mul (continuous_finsetSum _ fun i hi => continuous_const.mul (hg i hi)))
      |>.intervalIntegrable 0 t
  calc ‖∫ s in (0 : ℝ)..t, comm ((exp ((t - s) • P) * Q * exp (s • (P + Q))) a) b‖
      ≤ ∫ s in (0 : ℝ)..t, 2 * ∑ i ∈ G.crosses Y, G.kappa i * g i s :=
        norm_integral_le_of_norm_le ht (MeasureTheory.ae_of_all _ hbound) hgint
    _ = 2 * ∑ i ∈ G.crosses Y, G.kappa i * ∫ s in (0 : ℝ)..t, g i s := by
        rw [integral_const_mul]
        congr 1
        rw [integral_finsetSum (f := fun i s => G.kappa i * g i s) fun i hi =>
          (continuous_const.mul (hg i hi)).intervalIntegrable 0 t]
        exact Finset.sum_congr rfl fun i hi => integral_const_mul _ _

/-! ### The iteration -/

/-- The coefficient `c_k(t) = (2t)^{k+1} / (k+1)!`. -/
def coef (k : ℕ) (t : ℝ) : ℝ := (2 * t) ^ (k + 1) / ((k + 1).factorial : ℝ)

/-- The truncated bound after `n + 1` Duhamel steps:
`B_n(Y, X, t) = 2 (Σ_{k < n} c_k(t) P_{k+1}(Y, X) + c_n(t) K^{n+1})`. -/
def truncBound (X Y : Set Λ) (n : ℕ) (t : ℝ) : ℝ :=
  2 * (∑ k ∈ range n, coef k t * G.pathSumRec X (k + 1) Y + coef n t * G.totalStrength ^ (n + 1))

theorem coef_nonneg (k : ℕ) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ coef k t :=
  div_nonneg (pow_nonneg (by linarith) _) (Nat.cast_nonneg _)

@[fun_prop]
theorem continuous_coef (k : ℕ) : Continuous fun t => coef k t := by
  unfold coef; fun_prop

theorem continuous_truncBound (X Y : Set Λ) (n : ℕ) : Continuous (G.truncBound X Y n) := by
  unfold truncBound
  exact continuous_const.mul ((continuous_finsetSum _ fun k _ =>
    (continuous_coef k).mul continuous_const).add ((continuous_coef n).mul continuous_const))

/-- `∫_0^t c_k(s) ds = c_{k+1}(t) / 2`. -/
theorem integral_coef (k : ℕ) (t : ℝ) : ∫ s in (0 : ℝ)..t, coef k s = coef (k + 1) t / 2 := by
  have h : ∀ s : ℝ, coef k s = (2 ^ (k + 1) / ((k + 1).factorial : ℝ)) * s ^ (k + 1) := by
    intro s; unfold coef; rw [mul_pow]; ring
  simp_rw [h]
  rw [integral_const_mul, integral_pow, zero_pow (Nat.succ_ne_zero _), sub_zero]
  unfold coef
  rw [Nat.factorial_succ (k + 1), mul_pow]
  push_cast
  have hf : ((k + 1).factorial : ℝ) ≠ 0 := by positivity
  field_simp
  ring

/-- `∫_0^t B_n(S, X, s) ds = Σ_{k < n} c_{k+1}(t) P_{k+1}(S, X) + c_{n+1}(t) K^{n+1}`. -/
theorem integral_truncBound (X S : Set Λ) (n : ℕ) (t : ℝ) :
    ∫ s in (0 : ℝ)..t, G.truncBound X S n s =
      ∑ k ∈ range n, coef (k + 1) t * G.pathSumRec X (k + 1) S +
        coef (n + 1) t * G.totalStrength ^ (n + 1) := by
  unfold truncBound
  have hsum_int : IntervalIntegrable
      (fun s => ∑ k ∈ range n, coef k s * G.pathSumRec X (k + 1) S) MeasureTheory.volume 0 t :=
    (continuous_finsetSum _ fun k _ =>
      (continuous_coef k).mul continuous_const).intervalIntegrable 0 t
  have hrem_int : IntervalIntegrable (fun s => coef n s * G.totalStrength ^ (n + 1))
      MeasureTheory.volume 0 t :=
    ((continuous_coef n).mul continuous_const).intervalIntegrable 0 t
  rw [integral_const_mul, integral_add hsum_int hrem_int,
    integral_finsetSum (f := fun k s => coef k s * G.pathSumRec X (k + 1) S) fun k _ =>
      ((continuous_coef k).mul continuous_const).intervalIntegrable 0 t,
    integral_mul_const]
  simp only [integral_mul_const, integral_coef]
  rw [mul_add, Finset.mul_sum]
  congr 1
  · exact Finset.sum_congr rfl fun k _ => by ring
  · ring

/-- The integral of the constant majorant `2` of the bridge terms. -/
theorem integral_two (t : ℝ) : ∫ _ in (0 : ℝ)..t, (2 : ℝ) = coef 0 t := by
  rw [integral_const]; unfold coef; simp; ring

/-- The induction step's algebra: the majorant integrals sum to at most `B_{n+1}(Y, X, t)`. -/
theorem sum_integral_majorant_le (X Y : Set Λ) (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    2 * (∑ i ∈ G.bridge X Y, G.kappa i * coef 0 t +
      ∑ i ∈ G.through X Y, G.kappa i *
        (∑ k ∈ range n, coef (k + 1) t * G.pathSumRec X (k + 1) (G.supp i) +
          coef (n + 1) t * G.totalStrength ^ (n + 1))) ≤ G.truncBound X Y (n + 1) t := by
  unfold truncBound
  rw [Finset.sum_range_succ']
  simp only [zero_add, pathSumRec_one, pathSumRec_succ_succ']
  have hK : ∑ i ∈ G.through X Y, G.kappa i ≤ G.totalStrength := G.sum_kappa_le_totalStrength _
  have hc : 0 ≤ coef (n + 1) t := coef_nonneg _ ht
  have hKn : 0 ≤ G.totalStrength ^ (n + 1) := pow_nonneg G.totalStrength_nonneg _
  have hsum : ∑ i ∈ G.through X Y, G.kappa i *
      (∑ k ∈ range n, coef (k + 1) t * G.pathSumRec X (k + 1) (G.supp i) +
        coef (n + 1) t * G.totalStrength ^ (n + 1)) =
      ∑ k ∈ range n, coef (k + 1) t *
        ∑ i ∈ G.through X Y, G.kappa i * G.pathSumRec X (k + 1) (G.supp i) +
      coef (n + 1) t * G.totalStrength ^ (n + 1) * ∑ i ∈ G.through X Y, G.kappa i := by
    simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    congr 1
    · rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => by ring
    · refine Finset.sum_congr rfl fun i _ => by ring
  rw [hsum]
  have hbridge : ∑ i ∈ G.bridge X Y, G.kappa i * coef 0 t =
      coef 0 t * ∑ i ∈ G.bridge X Y, G.kappa i := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
  rw [hbridge]
  have hrem : coef (n + 1) t * G.totalStrength ^ (n + 1) * ∑ i ∈ G.through X Y, G.kappa i ≤
      coef (n + 1) t * G.totalStrength ^ (n + 1 + 1) := by
    rw [pow_succ, mul_assoc]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hK hKn) hc
  linarith

/-- M1a, Theorem 3.11 (iteration): for disjoint regions, unit `a`, `b` and `t ≥ 0`,
`‖[A(t), b]‖ ≤ 2 Σ_{k=1}^{n} (2t)^k/k! P_k(Y,X) + 2 (2tK)^{n+1}/(n+1)!`, for every `n`. -/
theorem norm_comm_evolve_le_truncBound (hc : Net.IsCausal (latticeIndex Λ) 𝒜) (n : ℕ) :
    ∀ {X Y : Set Λ}, Disjoint X Y → ∀ {a b : A}, a ∈ 𝒜 X → b ∈ 𝒜 Y → ‖a‖ ≤ 1 → ‖b‖ ≤ 1 →
      ∀ {t : ℝ}, 0 ≤ t → ‖comm (G.evolve t a) b‖ ≤ G.truncBound X Y n t := by
  classical
  induction n with
  | zero =>
    intro X Y hXY a b ha hb ha1 hb1 t ht
    have h := G.norm_comm_evolve_le_of_majorant hc hXY ha hb hb1 ht (fun _ _ => 2)
      (fun _ _ => continuous_const) (fun i _ s hs => ?_)
    · refine h.trans ?_
      simp only [integral_two, truncBound, range_zero, sum_empty, zero_add, pow_one]
      rw [← Finset.sum_mul]
      have := G.sum_kappa_le_totalStrength (G.crosses Y)
      have hc0 : 0 ≤ coef 0 t := coef_nonneg 0 ht
      nlinarith [mul_le_mul_of_nonneg_right this hc0]
    · exact (commNorm_le_two_mul_norm _ _ _).trans
        (by linarith [G.norm_evolve_le hs.1 a])
  | succ n ih =>
    intro X Y hXY a b ha hb ha1 hb1 t ht
    -- the majorant: `2` on the bridges, `B_n(S_i, X, ·)` on the throughs
    let g : ι → ℝ → ℝ := fun i s =>
      if Disjoint (G.supp i : Set Λ) X then G.truncBound X (G.supp i) n s else 2
    have hg : ∀ i ∈ G.crosses Y, Continuous (g i) := by
      intro i _
      by_cases hi : Disjoint (G.supp i : Set Λ) X
      · simpa [g, hi] using G.continuous_truncBound X (G.supp i) n
      · simpa [g, hi] using continuous_const
    have hmaj : ∀ i ∈ G.crosses Y, ∀ s ∈ Set.Icc 0 t,
        commNorm 𝒜 (G.supp i) (G.evolve s a) ≤ g i s := by
      intro i _ s hs
      by_cases hi : Disjoint (G.supp i : Set Λ) X
      · simp only [g, hi, ite_true]
        refine commNorm_le_of_forall 𝒜 _ fun b' hb' hb'1 => ?_
        exact ih hi.symm ha hb' ha1 hb'1 hs.1
      · simp only [g, hi, ite_false]
        exact (commNorm_le_two_mul_norm _ _ _).trans
          (by linarith [G.norm_evolve_le hs.1 a])
    refine (G.norm_comm_evolve_le_of_majorant hc hXY ha hb hb1 ht g hg hmaj).trans ?_
    have h1 : ∑ i ∈ G.bridge X Y, G.kappa i * ∫ s in (0 : ℝ)..t, g i s =
        ∑ i ∈ G.bridge X Y, G.kappa i * coef 0 t :=
      Finset.sum_congr rfl fun i hi => by
        have hnd : ¬ Disjoint (G.supp i : Set Λ) X :=
          Set.not_disjoint_iff_nonempty_inter.mpr (G.mem_bridge.mp hi).2
        simp only [g, hnd, ite_false, integral_two]
    have h2 : ∑ i ∈ G.through X Y, G.kappa i * ∫ s in (0 : ℝ)..t, g i s =
        ∑ i ∈ G.through X Y, G.kappa i *
          (∑ k ∈ range n, coef (k + 1) t * G.pathSumRec X (k + 1) (G.supp i) +
            coef (n + 1) t * G.totalStrength ^ (n + 1)) :=
      Finset.sum_congr rfl fun i hi => by
        simp only [g, (G.mem_through.mp hi).2, ite_true, G.integral_truncBound]
    rw [G.crosses_eq_bridge_union_through X Y, Finset.sum_union (G.disjoint_bridge_through X Y),
      h1, h2]
    exact G.sum_integral_majorant_le X Y n ht

/-! ### The master lemma -/

/-- The terms of the path series, `(2t)^{k+1}/(k+1)! · P_{k+1}(Y, X)`. -/
def seriesTerm (X Y : Set Λ) (t : ℝ) (k : ℕ) : ℝ := coef k t * G.pathSumRec X (k + 1) Y

theorem seriesTerm_nonneg (X Y : Set Λ) {t : ℝ} (ht : 0 ≤ t) (k : ℕ) :
    0 ≤ G.seriesTerm X Y t k :=
  mul_nonneg (coef_nonneg k ht) (G.pathSumRec_nonneg X _ Y)

theorem seriesTerm_le (X Y : Set Λ) {t : ℝ} (ht : 0 ≤ t) (k : ℕ) :
    G.seriesTerm X Y t k ≤ (2 * t * G.totalStrength) ^ (k + 1) / ((k + 1).factorial : ℝ) := by
  unfold seriesTerm coef
  rw [div_mul_eq_mul_div, mul_pow (2 * t)]
  gcongr
  exact G.pathSumRec_le X _ Y

/-- The path series converges (dominated by the exponential series of `2tK`). -/
theorem summable_seriesTerm (X Y : Set Λ) {t : ℝ} (ht : 0 ≤ t) :
    Summable (G.seriesTerm X Y t) := by
  have h := Real.summable_pow_div_factorial (2 * t * G.totalStrength)
  rw [← summable_nat_add_iff 1] at h
  exact Summable.of_nonneg_of_le (G.seriesTerm_nonneg X Y ht) (G.seriesTerm_le X Y ht) h

/-- The remainder `2 (2tK)^{n+1}/(n+1)!` tends to zero. -/
theorem tendsto_remainder (t : ℝ) :
    Filter.Tendsto (fun n : ℕ => 2 * (coef n t * G.totalStrength ^ (n + 1))) Filter.atTop
      (nhds 0) := by
  have h := FloorSemiring.tendsto_pow_div_factorial_atTop (2 * t * G.totalStrength)
  have h' := (h.comp (Filter.tendsto_add_atTop_nat 1)).const_mul 2
  rw [mul_zero] at h'
  refine h'.congr fun n => ?_
  simp only [Function.comp, coef, mul_pow]
  ring

/-- M1a, Theorem 3.12 for disjoint regions and unit `a`, `b`: the path series. -/
theorem norm_comm_evolve_le_tsum (hc : Net.IsCausal (latticeIndex Λ) 𝒜) {X Y : Set Λ}
    (hXY : Disjoint X Y) {a b : A} (ha : a ∈ 𝒜 X) (hb : b ∈ 𝒜 Y) (ha1 : ‖a‖ ≤ 1)
    (hb1 : ‖b‖ ≤ 1) {t : ℝ} (ht : 0 ≤ t) :
    ‖comm (G.evolve t a) b‖ ≤ 2 * ∑' k, G.seriesTerm X Y t k := by
  have hsum := G.summable_seriesTerm X Y ht
  have hlim : Filter.Tendsto
      (fun n : ℕ => 2 * ∑' k, G.seriesTerm X Y t k + 2 * (coef n t * G.totalStrength ^ (n + 1)))
      Filter.atTop (nhds (2 * ∑' k, G.seriesTerm X Y t k + 0)) :=
    tendsto_const_nhds.add (G.tendsto_remainder t)
  rw [add_zero] at hlim
  refine ge_of_tendsto' hlim fun n => ?_
  refine (G.norm_comm_evolve_le_truncBound hc n hXY ha hb ha1 hb1 ht).trans ?_
  unfold truncBound
  rw [mul_add]
  gcongr
  exact hsum.sum_le_tsum (range n) fun k _ => G.seriesTerm_nonneg X Y ht k

/-- Scaling: `[e^{tL}(r a), r' b] = (r r') [e^{tL} a, b]`. -/
theorem comm_evolve_smul (t : ℝ) (r r' : ℂ) (a b : A) :
    comm (G.evolve t (r • a)) (r' • b) = (r * r') • comm (G.evolve t a) b := by
  rw [(G.evolve t).map_smul, comm_smul_left, comm_smul_right, smul_smul]

/-- M1a, Theorem 3.12 for disjoint regions: the path series with `2‖a‖‖b‖`. -/
theorem liebRobinson_path (hc : Net.IsCausal (latticeIndex Λ) 𝒜) {X Y : Set Λ}
    (hXY : Disjoint X Y) {a b : A} (ha : a ∈ 𝒜 X) (hb : b ∈ 𝒜 Y) {t : ℝ} (ht : 0 ≤ t) :
    ‖comm (G.evolve t a) b‖ ≤ 2 * ‖a‖ * ‖b‖ * ∑' k, G.seriesTerm X Y t k := by
  rcases eq_or_ne a 0 with rfl | ha0
  · simp [comm]
  rcases eq_or_ne b 0 with rfl | hb0
  · simp [comm]
  have hna : 0 < ‖a‖ := norm_pos_iff.mpr ha0
  have hnb : 0 < ‖b‖ := norm_pos_iff.mpr hb0
  set a' : A := ((‖a‖⁻¹ : ℝ) : ℂ) • a with ha'
  set b' : A := ((‖b‖⁻¹ : ℝ) : ℂ) • b with hb'
  have ha'1 : ‖a'‖ ≤ 1 := by
    rw [ha', norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hna),
      inv_mul_cancel₀ hna.ne']
  have hb'1 : ‖b'‖ ≤ 1 := by
    rw [hb', norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hnb),
      inv_mul_cancel₀ hnb.ne']
  have ha'm : a' ∈ 𝒜 X := (𝒜 X).smul_mem ha _
  have hb'm : b' ∈ 𝒜 Y := (𝒜 Y).smul_mem hb _
  have h := G.norm_comm_evolve_le_tsum hc hXY ha'm hb'm ha'1 hb'1 ht
  have hpos : 0 < ‖a‖⁻¹ * ‖b‖⁻¹ := mul_pos (inv_pos.mpr hna) (inv_pos.mpr hnb)
  have hcs : comm (G.evolve t a') b' =
      ((‖a‖⁻¹ * ‖b‖⁻¹ : ℝ) : ℂ) • comm (G.evolve t a) b := by
    rw [ha', hb', G.comm_evolve_smul, Complex.ofReal_mul]
  rw [hcs, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos] at h
  rw [← le_div_iff₀' hpos] at h
  calc ‖comm (G.evolve t a) b‖ ≤ 2 * (∑' k, G.seriesTerm X Y t k) / (‖a‖⁻¹ * ‖b‖⁻¹) := h
    _ = 2 * ‖a‖ * ‖b‖ * ∑' k, G.seriesTerm X Y t k := by
        rw [div_eq_mul_inv, mul_inv, inv_inv, inv_inv]
        ring

open Classical in
/-- M1a, Theorem 3.12: the master lemma, for arbitrary regions. -/
theorem liebRobinson (hc : Net.IsCausal (latticeIndex Λ) 𝒜) (X Y : Set Λ) {a b : A}
    (ha : a ∈ 𝒜 X) (hb : b ∈ 𝒜 Y) {t : ℝ} (ht : 0 ≤ t) :
    ‖comm (G.evolve t a) b‖ ≤
      2 * ‖a‖ * ‖b‖ * ((if (X ∩ Y).Nonempty then 1 else 0) + ∑' k, G.seriesTerm X Y t k) := by
  have hts : 0 ≤ ∑' k, G.seriesTerm X Y t k := tsum_nonneg (G.seriesTerm_nonneg X Y ht)
  have hab : 0 ≤ 2 * ‖a‖ * ‖b‖ := by positivity
  by_cases hXY : (X ∩ Y).Nonempty
  · simp only [hXY, ite_true]
    calc ‖comm (G.evolve t a) b‖ ≤ 2 * ‖G.evolve t a‖ * ‖b‖ := norm_comm_le _ _
      _ ≤ 2 * ‖a‖ * ‖b‖ := by gcongr; exact G.norm_evolve_le ht a
      _ = 2 * ‖a‖ * ‖b‖ * 1 := (mul_one _).symm
      _ ≤ 2 * ‖a‖ * ‖b‖ * (1 + ∑' k, G.seriesTerm X Y t k) := by gcongr; linarith
  · simp only [hXY, ite_false, zero_add]
    exact G.liebRobinson_path hc (Set.disjoint_iff_inter_eq_empty.mpr
      (Set.not_nonempty_iff_eq_empty.mp hXY)) ha hb ht

/-- `C_{X,Y}(t)`: the supremum of `‖[A(t), b]‖` over unit `a ∈ 𝒜 X` and unit `b ∈ 𝒜 Y`
(M1a, eq. (2)). -/
def commBound (X Y : Set Λ) (t : ℝ) : ℝ :=
  sSup ((fun p : A × A => ‖comm (G.evolve t p.1) p.2‖) ''
    {p | p.1 ∈ 𝒜 X ∧ ‖p.1‖ ≤ 1 ∧ p.2 ∈ 𝒜 Y ∧ ‖p.2‖ ≤ 1})

open Classical in
/-- M1a, Theorem 3.12 in the supremum form:
`C_{X,Y}(t) ≤ 2 [X ∩ Y ≠ ∅] + 2 Σ_{k ≥ 1} (2t)^k/k! P_k(Y, X)`. -/
theorem commBound_le (hc : Net.IsCausal (latticeIndex Λ) 𝒜) (X Y : Set Λ) {t : ℝ}
    (ht : 0 ≤ t) :
    G.commBound X Y t ≤
      2 * ((if (X ∩ Y).Nonempty then 1 else 0) + ∑' k, G.seriesTerm X Y t k) := by
  refine csSup_le ⟨‖comm (G.evolve t 0) 0‖, (0, 0), ⟨zero_mem _, by simp, zero_mem _, by simp⟩,
    rfl⟩ ?_
  rintro _ ⟨⟨a, b⟩, ⟨ha, ha1, hb, hb1⟩, rfl⟩
  have h := G.liebRobinson hc X Y ha hb ht
  have hts : 0 ≤ ∑' k, G.seriesTerm X Y t k := tsum_nonneg (G.seriesTerm_nonneg X Y ht)
  have hS : 0 ≤ (if (X ∩ Y).Nonempty then (1 : ℝ) else 0) + ∑' k, G.seriesTerm X Y t k := by
    split_ifs <;> linarith
  calc ‖comm (G.evolve t a) b‖ ≤ 2 * ‖a‖ * ‖b‖ * _ := h
    _ ≤ 2 * 1 * 1 * _ := by gcongr
    _ = 2 * _ := by ring

end LocalGenerators

end LocalityLean

end
