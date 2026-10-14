/-
Copyright (c) 2026 LocalityLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LocalityLean contributors
-/
import Mathlib.Analysis.SpecialFunctions.Exponential
import LocalityLean.Bosonic.Harmonic

/-!
# The harmonic chain

The chain `H = ½ ∑_x (p_x² + ω² q_x²) + ½ λ ∑_x (q_x - q_{x+1})²` on `n` sites with open ends
(M5, Definition 2.6): its potential matrix `A`, its label generator `K` with
`(Kf)^q = -A f^p`, `(Kf)^p = f^q` (the transpose of Hamilton's matrix), the generator condition,
the range `1`, the row sums (M5, Proposition 7.1), and the witness that momenta at neighbouring
sites fail to commute after evolution (M5, Proposition 7.3).

## Main results

* `LocalityLean.Bosonic.chainPotential`, `chain`, `chain_isQuadraticGenerator`,
  `chain_hasRange_one`, `chain_rowSumLE`.
* `LocalityLean.Bosonic.exists_comm_alpha_ne_zero`.
-/

namespace LocalityLean.Bosonic

open scoped Matrix

variable (n : ℕ) (ω lam : ℝ)

/-- Whether two sites of the chain are neighbours. -/
def Adj (x y : Fin n) : Prop := (x : ℕ) + 1 = y ∨ (y : ℕ) + 1 = x

instance : DecidableRel (Adj n) := fun _ _ => inferInstanceAs (Decidable (_ ∨ _))

/-- The number of neighbours of a site. -/
def degree (x : Fin n) : ℕ := (Finset.univ.filter fun y => Adj n x y).card

/-- M5, Definition 2.6: the potential matrix `A` of the chain,
`A_{xx} = ω² + λ·deg(x)`, `A_{x,x±1} = -λ`. -/
def chainPotential : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun x y => if x = y then ω ^ 2 + lam * degree n x else if Adj n x y then -lam else 0

/-- M5, Definition 2.6: the label generator of the chain, `(Kf)^q = -A f^p`, `(Kf)^p = f^q`. -/
def chain : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℝ :=
  Matrix.of fun b a =>
    if b.2 = 0 ∧ a.2 = 1 then -(chainPotential n ω lam b.1 a.1)
    else if b.2 = 1 ∧ a.2 = 0 ∧ b.1 = a.1 then 1 else 0

theorem adj_comm {x y : Fin n} : Adj n x y ↔ Adj n y x := Or.comm

theorem chainPotential_isSymm : (chainPotential n ω lam).IsSymm := by
  refine Matrix.IsSymm.ext fun x y => ?_
  simp only [chainPotential, Matrix.of_apply]
  by_cases h : x = y
  · subst h; rfl
  · rw [ite_eq_right_iff.2 fun h' => absurd h'.symm h, ite_eq_right_iff.2 fun h' => absurd h' h]
    simp only [adj_comm n (x := y) (y := x)]

/-- M5, Proposition 7.1: the chain's generator is quadratic. -/
theorem chain_isQuadraticGenerator : IsQuadraticGenerator (chain n ω lam) := by
  unfold IsQuadraticGenerator
  ext ⟨x, i⟩ ⟨y, j⟩
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply, Fintype.sum_prod_type,
    Fin.sum_univ_two, chain, Omega, Matrix.of_apply, Matrix.zero_apply]
  fin_cases i <;> fin_cases j
  · rcases eq_or_ne x y with rfl | h
    · simp
    · simp [h, Ne.symm h]
  · simp
  · simp
  · simp [(chainPotential_isSymm n ω lam).apply x y]

/-- The distance on the chain. -/
def chainDist (x y : Fin n) : ℝ := |((x : ℕ) : ℝ) - ((y : ℕ) : ℝ)|

theorem chainDist_self (x : Fin n) : chainDist n x x = 0 := by simp [chainDist]

theorem chainDist_triangle (x y z : Fin n) :
    chainDist n x z ≤ chainDist n x y + chainDist n y z := by
  unfold chainDist
  exact abs_sub_le _ _ _

/-- M5, Proposition 7.1: range `1`. -/
theorem chain_hasRange_one : HasRange (chain n ω lam) Prod.fst (chainDist n) 1 := by
  intro b a h
  have hfar : ∀ u v : ℕ, (u + 1 = v ∨ v + 1 = u ∨ u = v) → |(u : ℝ) - v| ≤ 1 := by
    rintro u v (rfl | rfl | rfl) <;> push_cast <;> simp
  have hne : b.1 ≠ a.1 := fun he => by
    have := hfar b.1 a.1 (Or.inr (Or.inr (congrArg Fin.val he)))
    exact absurd h (not_lt.2 this)
  have hadj : ¬ Adj n b.1 a.1 := fun hab => by
    have := hfar b.1 a.1 (by unfold Adj at hab; tauto)
    exact absurd h (not_lt.2 this)
  simp [chain, chainPotential, hne, hadj]

/-- M5, Proposition 7.1: row sums at most `max 1 (ω² + 4λ)` for `λ ≥ 0`. -/
theorem chain_rowSumLE (hl : 0 ≤ lam) : RowSumLE (chain n ω lam) (max 1 (ω ^ 2 + 4 * lam)) := by
  have hdeg : ∀ x : Fin n, (degree n x : ℝ) ≤ 2 := by
    intro x
    have h1 : ∀ p : ℕ → Prop, [DecidablePred p] → (∀ u v, p u → p v → u = v) →
        (Finset.univ.filter fun y : Fin n => p y).card ≤ 1 := by
      intro p _ hp
      refine Finset.card_le_one.2 fun u hu v hv => Fin.ext ?_
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu hv
      exact hp _ _ hu hv
    have hsub : Finset.univ.filter (Adj n x) ⊆
        Finset.univ.filter (fun y : Fin n => (x : ℕ) + 1 = y) ∪
          Finset.univ.filter (fun y : Fin n => (y : ℕ) + 1 = x) := by
      intro y
      simp [Adj]
    have hle : degree n x ≤ 2 := by
      refine (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans ?_)
      have := h1 (fun y => (x : ℕ) + 1 = y) fun u v hu hv => hu.symm.trans hv
      have := h1 (fun y => y + 1 = (x : ℕ)) fun u v hu hv => by omega
      omega
    exact_mod_cast hle
  rintro ⟨x, i⟩
  rw [Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two]
  revert i
  rw [Fin.forall_fin_two]
  refine ⟨le_max_of_le_right ?_, le_max_of_le_left ?_⟩
  · have hA : ∀ y, |chainPotential n ω lam x y| =
        (if x = y then ω ^ 2 + lam * degree n x else 0) + (if Adj n x y then lam else 0) := by
      intro y
      simp only [chainPotential, Matrix.of_apply]
      by_cases hxy : x = y
      · subst hxy
        have : ¬ Adj n x x := by unfold Adj; omega
        rw [ite_eq_left_iff.2 fun h => absurd rfl h, ite_eq_left_iff.2 fun h => absurd rfl h,
          ite_eq_right_iff.2 fun h => absurd h this, add_zero]
        exact abs_of_nonneg (by positivity)
      · by_cases hadj : Adj n x y <;> simp [hxy, hadj, abs_of_nonneg hl]
    have hs : ∑ y, (if Adj n x y then lam else 0) = (degree n x : ℝ) * lam := by
      rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
      rfl
    suffices h : ω ^ 2 + lam * degree n x + (degree n x : ℝ) * lam ≤ ω ^ 2 + 4 * lam by
      simpa [chain, hA, Finset.sum_add_distrib, hs] using h
    nlinarith [hdeg x]
  · simp [chain, apply_ite (abs : ℝ → ℝ)]

open scoped Matrix.Norms.Operator in
/-- An entry of `e^{tK}` has derivative `K_{ba}` at `t = 0`. -/
private theorem hasDerivAt_exp_smul_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : Matrix ι ι ℝ) (b a : ι) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp (t • K) b a) (K b a) 0 := by
  have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) K (0 : ℝ)
  rw [zero_smul, NormedSpace.exp_zero, one_mul] at h
  have hL := (LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℝ b a)).hasFDerivAt
    |>.comp_hasDerivAt (0 : ℝ) h
  convert hL using 1
  · rfl
  · rfl

/-- M5, Proposition 7.3: for `λ > 0` on a chain of at least two sites, the momenta at the sites
`0` and `1` do not commute after some positive time. -/
theorem exists_comm_alpha_ne_zero (hn : 2 ≤ n) (hl : 0 < lam) :
    ∃ t : ℝ, 0 < t ∧
      comm (alpha (chain_isQuadraticGenerator n ω lam) t
          (BosonicLean.Weyl.wCCR (sigma (Fin n)) (Pi.single (⟨0, by omega⟩, 1) 1)))
        (BosonicLean.Weyl.wCCR (sigma (Fin n)) (Pi.single (⟨1, by omega⟩, 1) 1)) ≠ 0 := by
  set i0 : Fin n := ⟨0, by omega⟩
  set i1 : Fin n := ⟨1, by omega⟩
  set K := chain n ω lam
  have h10 : i1 ≠ i0 := fun h => by simpa [i0, i1] using congrArg Fin.val h
  have hKe : K (i1, 0) (i0, 1) = lam := by
    have hadj : Adj n i1 i0 := Or.inr rfl
    simp [K, chain, chainPotential, h10, hadj]
  have hφ : ∀ t, sigma (Fin n) (flow K t *ᵥ Pi.single (i0, 1) 1) (Pi.single (i1, 1) 1) =
      NormedSpace.exp (t • K) (i1, 0) (i0, 1) := by
    intro t
    rw [sigma_apply]
    simp [Matrix.mulVec_single, Pi.single_apply, flow]
  have hd := hasDerivAt_exp_smul_apply K (i1, 0) (i0, 1)
  rw [hKe] at hd
  obtain ⟨φ, hφe⟩ : ∃ φ : ℝ → ℝ, ∀ t, NormedSpace.exp (t • K) (i1, 0) (i0, 1) = φ t :=
    ⟨_, fun _ => rfl⟩
  simp only [hφe] at hd hφ
  have hφ0 : φ 0 = 0 := by rw [← hφe]; simp [h10]
  have e1 : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), 0 < t⁻¹ • (φ (0 + t) - φ 0) :=
    hd.tendsto_slope_zero_right.eventually_const_lt hl
  have e2 : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), φ t < 2 * Real.pi :=
    nhdsWithin_le_nhds <| hd.continuousAt.tendsto.eventually_lt_const <| by
      rw [hφ0]; positivity
  have e3 : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), 0 < t := self_mem_nhdsWithin
  obtain ⟨t, h1, h2, h3⟩ := (e1.and (e2.and e3)).exists
  refine ⟨t, h3, fun h0 => ?_⟩
  rw [zero_add, hφ0, sub_zero, smul_eq_mul] at h1
  have hpos : 0 < φ t := pos_of_mul_pos_right h1 (inv_pos.2 h3).le
  have hn := congrArg norm h0
  rw [alpha_wCCR, norm_comm_wCCR_eq_sin, hφ, norm_zero] at hn
  have hs : 0 < Real.sin (φ t / 2) := Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith)
  have := abs_pos.2 hs.ne'
  linarith

end LocalityLean.Bosonic
