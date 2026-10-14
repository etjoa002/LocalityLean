/-
Copyright (c) 2026 LocalityLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LocalityLean contributors
-/
import LocalityLean.Core.Decay

/-!
# Time reversal (M1b, Theorem 4.6)

The negated family `G⁻ = (S_i, -L_i, κ_i)` satisfies (G1) and (G2) whenever `G` does; (G3) for
`G⁻` is the hypothesis that `e^{-tL_J}` is a contraction for `t ≥ 0`, which automorphism groups
satisfy. Since `e^{tL} = e^{|t|(-L)}` for `t < 0` and the paths, counts and walk weights depend
only on the supports and strengths, the path-sum bound and its closed forms hold for every real
time with `|t|` in place of `t`.

## Main definitions

* `LocalityLean.LocalGenerators.NegContractive`, `LocalityLean.LocalGenerators.neg`.

## Main statements

* `LocalityLean.LocalGenerators.liebRobinson_abs`, `liebRobinson_walk_abs`,
  `liebRobinson_decay_abs`.
-/

noncomputable section

namespace LocalityLean

open LinearAQFT Finset

variable {Λ : Type*} {A : Type*} [CStarAlgebra A]
variable {ι : Type*} [Fintype ι] {𝒜 : Net (Set Λ) A} (G : LocalGenerators ι 𝒜)

namespace LocalGenerators

/-- (G3) for the negated family: every `e^{-tL_J}` is a contraction for `t ≥ 0`. -/
def NegContractive : Prop :=
  ∀ (J : Finset ι) (t : ℝ), 0 ≤ t → ‖NormedSpace.exp (t • ∑ i ∈ J, -G.L i)‖ ≤ 1

/-- The negated family `G⁻` (M1b, Definition 2.6), given (G3) for it. -/
def neg (h : G.NegContractive) : LocalGenerators ι 𝒜 where
  supp := G.supp
  L := fun i => -G.L i
  kappa := G.kappa
  kappa_nonneg := G.kappa_nonneg
  local_in_arg := fun i c => by
    rw [neg_apply, norm_neg]
    exact G.local_in_arg i c
  maps_into := fun i Z a ha => by
    rw [neg_apply]
    exact neg_mem (G.maps_into i Z a ha)
  contraction := h

variable {G}

section Transport

variable (h : G.NegContractive)

theorem neg_supp : (G.neg h).supp = G.supp := rfl

theorem neg_kappa : (G.neg h).kappa = G.kappa := rfl

theorem neg_total : (G.neg h).total = -G.total := by
  simp [total, subfamily, neg, Finset.sum_neg_distrib]

theorem neg_evolve (t : ℝ) : (G.neg h).evolve t = G.evolve (-t) := by
  rw [evolve, evolve, neg_total, smul_neg, neg_smul]

theorem neg_crosses (Y : Set Λ) : (G.neg h).crosses Y = G.crosses Y := rfl

theorem neg_bridge (X Y : Set Λ) : (G.neg h).bridge X Y = G.bridge X Y := rfl

theorem neg_through (X Y : Set Λ) : (G.neg h).through X Y = G.through X Y := rfl

theorem neg_pathSumRec (X : Set Λ) (k : ℕ) (Y : Set Λ) :
    (G.neg h).pathSumRec X k Y = G.pathSumRec X k Y := by
  induction k using Nat.strong_induction_on generalizing Y with
  | _ k ih =>
    rcases k with _ | _ | k
    · rw [pathSumRec_zero, pathSumRec_zero]
    · rw [pathSumRec_one, pathSumRec_one, neg_bridge, neg_kappa]
    · rw [pathSumRec_succ_succ, pathSumRec_succ_succ, neg_through, neg_kappa]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [ih (k + 1) (by omega), neg_supp]

theorem neg_seriesTerm (X Y : Set Λ) (t : ℝ) (k : ℕ) :
    (G.neg h).seriesTerm X Y t k = G.seriesTerm X Y t k := by
  unfold seriesTerm
  rw [neg_pathSumRec]

theorem neg_touched : (G.neg h).touched = G.touched := rfl

theorem neg_siteMatrix (u v : Λ) : (G.neg h).siteMatrix u v = G.siteMatrix u v := rfl

theorem neg_walk (k : ℕ) (y x : Λ) : (G.neg h).walk k y x = G.walk k y x := by
  induction k generalizing y x with
  | zero =>
    by_cases hyx : y = x
    · subst hyx; rw [(G.neg h).walk_zero_self, G.walk_zero_self]
    · rw [(G.neg h).walk_zero_of_ne hyx, G.walk_zero_of_ne hyx]
  | succ k ih =>
    rw [walk_succ, walk_succ, neg_touched]
    exact Finset.sum_congr rfl fun z _ => by rw [neg_siteMatrix, ih]

theorem neg_boundary (Y : Set Λ) : (G.neg h).boundary Y = G.boundary Y := rfl

theorem neg_regionSites (X : Set Λ) : (G.neg h).regionSites X = G.regionSites X := rfl

theorem neg_walkSum (X Y : Set Λ) (k : ℕ) : (G.neg h).walkSum X Y k = G.walkSum X Y k := by
  unfold walkSum
  rw [neg_boundary, neg_regionSites]
  exact Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => neg_walk h k y x

theorem neg_walkTerm (X Y : Set Λ) (t : ℝ) (k : ℕ) :
    (G.neg h).walkTerm X Y t k = G.walkTerm X Y t k := by
  unfold walkTerm
  rw [neg_walkSum]

theorem neg_kernelSum (K : DecayKernel Λ) (X Y : Set Λ) :
    (G.neg h).kernelSum K X Y = G.kernelSum K X Y := by
  unfold kernelSum
  rw [neg_boundary, neg_regionSites]

theorem neg_isFBound {K : DecayKernel Λ} {N : ℝ} (hN : G.IsFBound K N) :
    (G.neg h).IsFBound K N :=
  ⟨hN.1, fun x y => by rw [neg_siteMatrix]; exact hN.2 x y⟩

end Transport

variable (G)

open Classical in
/-- M1b, Theorem 4.6 (time reversal) for the path-sum bound: for every `t ∈ ℝ`,
`‖[A(t), b]‖ ≤ 2‖a‖‖b‖ ([X ∩ Y ≠ ∅] + Σ_{k ≥ 1} (2|t|)^k/k! P_k(Y, X))`. -/
theorem liebRobinson_abs (hc : Net.IsCausal (latticeIndex Λ) 𝒜) (h : G.NegContractive)
    (X Y : Set Λ) {a b : A} (ha : a ∈ 𝒜 X) (hb : b ∈ 𝒜 Y) (t : ℝ) :
    ‖comm (G.evolve t a) b‖ ≤
      2 * ‖a‖ * ‖b‖ * ((if (X ∩ Y).Nonempty then 1 else 0) + ∑' k, G.seriesTerm X Y |t| k) := by
  rcases le_or_gt 0 t with ht | ht
  · rw [abs_of_nonneg ht]
    exact G.liebRobinson hc X Y ha hb ht
  · rw [abs_of_neg ht]
    have h' := (G.neg h).liebRobinson hc X Y ha hb (t := -t) (by linarith)
    simp only [neg_evolve, neg_neg, neg_seriesTerm] at h'
    exact h'

open Classical in
/-- Time reversal for the walk series (Theorem 3.6 for every `t ∈ ℝ`). -/
theorem liebRobinson_walk_abs (hc : Net.IsCausal (latticeIndex Λ) 𝒜) (h : G.NegContractive)
    (X Y : Set Λ) {a b : A} (ha : a ∈ 𝒜 X) (hb : b ∈ 𝒜 Y) (t : ℝ) :
    ‖comm (G.evolve t a) b‖ ≤
      2 * ‖a‖ * ‖b‖ * ((if (X ∩ Y).Nonempty then 1 else 0) + ∑' k, G.walkTerm X Y |t| k) := by
  rcases le_or_gt 0 t with ht | ht
  · rw [abs_of_nonneg ht]
    exact G.liebRobinson_walk hc X Y ha hb ht
  · rw [abs_of_neg ht]
    have h' := (G.neg h).liebRobinson_walk hc X Y ha hb (t := -t) (by linarith)
    simp only [neg_evolve, neg_neg, neg_walkTerm] at h'
    exact h'

open Classical in
/-- Time reversal for the decay-function form (Theorem 3.8 for every `t ∈ ℝ`). -/
theorem liebRobinson_decay_abs (hc : Net.IsCausal (latticeIndex Λ) 𝒜) (h : G.NegContractive)
    (K : DecayKernel Λ) {N : ℝ} (hN : G.IsFBound K N) (X Y : Set Λ) {a b : A} (ha : a ∈ 𝒜 X)
    (hb : b ∈ 𝒜 Y) (t : ℝ) :
    ‖comm (G.evolve t a) b‖ ≤
      2 * ‖a‖ * ‖b‖ * ((if (X ∩ Y).Nonempty then 1 else 0) +
        (Real.exp (2 * N * K.CF * |t|) - 1) / K.CF * G.kernelSum K X Y) := by
  rcases le_or_gt 0 t with ht | ht
  · rw [abs_of_nonneg ht]
    exact G.liebRobinson_decay hc K hN X Y ha hb ht
  · rw [abs_of_neg ht]
    have h' := (G.neg h).liebRobinson_decay hc K (neg_isFBound h hN) X Y ha hb (t := -t)
      (by linarith)
    simp only [neg_evolve, neg_neg, neg_kernelSum] at h'
    exact h'

end LocalGenerators

end LocalityLean

end
