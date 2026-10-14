/-
Copyright (c) 2026 LocalityLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LocalityLean contributors
-/
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Duhamel's identity and the invariance lemma

For bounded operators `P, Q` on a Banach space, or more generally elements of a complete normed
real algebra,
`exp (t (P + Q)) = exp (t P) + ∫_0^t exp ((t - s) P) Q exp (s (P + Q)) ds` (M1a, Lemma 3.3); and
a closed subspace mapped into itself by `P` is mapped into itself by `exp (t P)` (M1a,
Lemma 3.4). Neither is in Mathlib at the pin.

## Main statements

* `LocalityLean.duhamel`.
* `LocalityLean.exp_apply_mem_of_maps_into`.
-/

noncomputable section

namespace LocalityLean

open NormedSpace intervalIntegral

section Duhamel

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

/-- The derivative of `s ↦ exp ((t - s) • P)` is `-(exp ((t - s) • P) * P)`. -/
theorem hasDerivAt_exp_sub_smul (P : 𝔸) (t s : ℝ) :
    HasDerivAt (fun s : ℝ => exp ((t - s) • P)) (-(exp ((t - s) • P) * P)) s := by
  have h1 : HasDerivAt (fun u : ℝ => exp (u • P)) (exp ((t - s) • P) * P) (t - s) :=
    hasDerivAt_exp_smul_const P (t - s)
  have h2 : HasDerivAt (fun s : ℝ => t - s) (-1 : ℝ) s := (hasDerivAt_id s).const_sub t
  have := h1.scomp s h2
  rw [neg_one_smul] at this
  exact this

/-- Continuity of `s ↦ exp (s • P)`. -/
theorem continuous_exp_smul (P : 𝔸) : Continuous fun s : ℝ => exp (s • P) :=
  continuous_iff_continuousAt.2 fun s => (hasDerivAt_exp_smul_const P s).continuousAt

/-- Continuity of `s ↦ exp ((t - s) • P)`. -/
theorem continuous_exp_sub_smul (P : 𝔸) (t : ℝ) : Continuous fun s : ℝ => exp ((t - s) • P) :=
  continuous_iff_continuousAt.2 fun s => (hasDerivAt_exp_sub_smul P t s).continuousAt

/-- M1a, Lemma 3.3 (Duhamel's identity):
`exp (t (P + Q)) = exp (t P) + ∫_0^t exp ((t - s) P) Q exp (s (P + Q)) ds`. -/
theorem duhamel (P Q : 𝔸) (t : ℝ) :
    exp (t • (P + Q)) =
      exp (t • P) + ∫ s in (0 : ℝ)..t, exp ((t - s) • P) * Q * exp (s • (P + Q)) := by
  let f : ℝ → 𝔸 := fun s => exp ((t - s) • P) * exp (s • (P + Q))
  have hderiv : ∀ s, HasDerivAt f (exp ((t - s) • P) * Q * exp (s • (P + Q))) s := by
    intro s
    have h1 := hasDerivAt_exp_sub_smul P t s
    have h2 : HasDerivAt (fun s : ℝ => exp (s • (P + Q))) ((P + Q) * exp (s • (P + Q))) s :=
      hasDerivAt_exp_smul_const' (P + Q) s
    have := h1.mul h2
    convert this using 1
    noncomm_ring
  have hcont : Continuous fun s : ℝ => exp ((t - s) • P) * Q * exp (s • (P + Q)) :=
    ((continuous_exp_sub_smul P t).mul continuous_const).mul (continuous_exp_smul (P + Q))
  have hint := integral_eq_sub_of_hasDerivAt (fun s _ => hderiv s) (hcont.intervalIntegrable 0 t)
  have hft : f t = exp (t • (P + Q)) := by simp [f]
  have hf0 : f 0 = exp (t • P) := by simp [f]
  rw [hft, hf0] at hint
  rw [hint, add_sub_cancel]

end Duhamel

section Invariance

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- Powers of `P` preserve a submodule that `P` preserves. -/
theorem pow_apply_mem_of_maps_into (P : E →L[ℂ] E) (M : Submodule ℂ E)
    (hP : ∀ a ∈ M, P a ∈ M) (k : ℕ) : ∀ a ∈ M, (P ^ k) a ∈ M := by
  induction k with
  | zero => intro a ha; simpa using ha
  | succ k ih =>
    intro a ha
    rw [pow_succ]
    exact ih (P a) (hP a ha)

set_option maxHeartbeats 400000 in
-- the exponential series on the operator space and its evaluation at `a` are unified through
-- the real-algebra structure of `E →L[ℂ] E`, which is slow
/-- M1a, Lemma 3.4 (invariance): a closed subspace mapped into itself by `P` is mapped into
itself by `exp (t • P)`. -/
theorem exp_apply_mem_of_maps_into (P : E →L[ℂ] E) (M : Submodule ℂ E)
    (hM : IsClosed (M : Set E)) (hP : ∀ a ∈ M, P a ∈ M) (t : ℝ) :
    ∀ a ∈ M, exp (t • P) a ∈ M := by
  intro a ha
  have hser : HasSum (fun n : ℕ => ((n.factorial : ℝ)⁻¹ : ℝ) • (t • P) ^ n) (exp (t • P)) :=
    exp_series_hasSum_exp' (𝕂 := ℝ) (t • P)
  have hsum := (ContinuousLinearMap.apply ℂ E a).hasSum hser
  have htP : ∀ b ∈ M, (t • P) b ∈ M := fun b hb => by
    rw [_root_.smul_apply]
    exact M.smul_of_tower_mem t (hP b hb)
  refine hM.mem_of_tendsto hsum.tendsto_sum_nat (Filter.Eventually.of_forall fun n => ?_)
  refine M.sum_mem fun i _ => ?_
  rw [ContinuousLinearMap.apply_apply, _root_.smul_apply]
  exact M.smul_of_tower_mem _ (pow_apply_mem_of_maps_into (t • P) M htP i a ha)

end Invariance

end LocalityLean

end
