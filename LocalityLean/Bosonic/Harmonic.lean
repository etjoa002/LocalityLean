/-
Copyright (c) 2026 LocalityLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LocalityLean contributors
-/
import BosonicLean.Weyl.System
import BosonicLean.Weyl.Relabel
import LocalityLean.Bosonic.Banded
import LocalityLean.Bosonic.Phase
import LocalityLean.Core.Derivation

/-!
# Quadratic generators and the harmonic Lieb-Robinson bound

A quadratic generator is a real matrix `K` on the phase space with `Kᵀ Ω + Ω K = 0` (M5,
Definition 2.4; for a quadratic Hamiltonian in the labelling `W(f) = e^{i f·ξ}` it is the
transpose of Hamilton's matrix). Its flow `T_t = e^{tK}` is a one-parameter group of symplectic
maps (M5, Proposition 4.1), and the dynamics `α_t` is BosonicLean's automorphism of the CCR
algebra induced by `T_t`, with `α_t(W f) = W(T_t f)`.

The Weyl relation gives `‖[W f, W g]‖ = |e^{-iσ(f,g)} - 1| ≤ |σ(f, g)|` (M5, Theorem 3.2), and
the entrywise bound of `LocalityLean/Bosonic/Banded.lean` gives the harmonic bound (M5,
Theorem 6.1)
`‖[α_t(W f), W g]‖ ≤ |σ(T_t f, g)| ≤ ∑_{b ∈ Y'} ∑_{a ∈ X'} (e^{|t||K|})_{ba} |f_a| |g_{b̄}|`
and its range and light-cone forms (M5, Corollary 6.2).

## Main results

* `LocalityLean.Bosonic.IsQuadraticGenerator`, `flow`, `flow_symplectic`, `flowEquiv`, `alpha`,
  `alpha_wCCR`.
* `LocalityLean.Bosonic.comm_wCCR_eq`, `norm_comm_wCCR_eq`, `norm_comm_wCCR_le`.
* `LocalityLean.Bosonic.liebRobinson_weyl`, `liebRobinson_weyl_geom`, `liebRobinson_weyl_cone`.
-/

namespace LocalityLean.Bosonic

open scoped Matrix
open BosonicLean BosonicLean.Weyl

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-- M5, Definition 2.4: a quadratic generator, `Kᵀ Ω + Ω K = 0`, the matrix form of
`σ(Ku, v) + σ(u, Kv) = 0`. -/
def IsQuadraticGenerator (K : Matrix (Λ × Fin 2) (Λ × Fin 2) ℝ) : Prop :=
  Kᵀ * Omega Λ + Omega Λ * K = 0

/-- The bilinear form of the generator condition. -/
theorem IsQuadraticGenerator.sigma_mulVec_add {K : Matrix (Λ × Fin 2) (Λ × Fin 2) ℝ}
    (hK : IsQuadraticGenerator K) (u v : Phase Λ) :
    sigma Λ (K *ᵥ u) v + sigma Λ u (K *ᵥ v) = 0 := by
  have h := congrArg (fun M => u ⬝ᵥ (M *ᵥ v)) hK
  simp only [Matrix.add_mulVec, Matrix.zero_mulVec, dotProduct_zero, dotProduct_add,
    ← Matrix.mulVec_mulVec] at h
  rw [Matrix.dotProduct_mulVec u Kᵀ, Matrix.vecMul_transpose] at h
  rw [sigma, Matrix.toBilin'_apply', Matrix.toBilin'_apply']
  exact h

/-- The flow `T_t = e^{tK}` of a generator. -/
noncomputable def flow (K : Matrix (Λ × Fin 2) (Λ × Fin 2) ℝ) (t : ℝ) :
    Matrix (Λ × Fin 2) (Λ × Fin 2) ℝ :=
  NormedSpace.exp (t • K)

theorem flow_zero (K : Matrix (Λ × Fin 2) (Λ × Fin 2) ℝ) : flow K 0 = 1 := by
  simp [flow]

/-- M5, Proposition 4.1: the group law. -/
theorem flow_add (K : Matrix (Λ × Fin 2) (Λ × Fin 2) ℝ) (s t : ℝ) :
    flow K (s + t) = flow K s * flow K t := by
  unfold flow
  rw [add_smul]
  exact Matrix.exp_add_of_commute _ _ ((Commute.refl K).smul_left s |>.smul_right t)

theorem flow_mul_flow_neg (K : Matrix (Λ × Fin 2) (Λ × Fin 2) ℝ) (t : ℝ) :
    flow K t * flow K (-t) = 1 := by
  rw [← flow_add, add_neg_cancel, flow_zero]

theorem flow_neg_mul_flow (K : Matrix (Λ × Fin 2) (Λ × Fin 2) ℝ) (t : ℝ) :
    flow K (-t) * flow K t = 1 := by
  rw [← flow_add, neg_add_cancel, flow_zero]

/-- M5, Proposition 4.1: the flow of a quadratic generator is symplectic,
`T_tᵀ Ω T_t = Ω`. -/
theorem IsQuadraticGenerator.flow_symplectic {K : Matrix (Λ × Fin 2) (Λ × Fin 2) ℝ}
    (hK : IsQuadraticGenerator K) (t : ℝ) :
    (flow K t)ᵀ * Omega Λ * flow K t = Omega Λ := by
  have hΩ : -Omega Λ * Omega Λ = 1 := by rw [neg_mul, Omega_mul_Omega, neg_neg]
  have hinv : (Omega Λ)⁻¹ = -Omega Λ := Matrix.inv_eq_left_inv hΩ
  have hU : IsUnit (Omega Λ) :=
    ⟨⟨Omega Λ, -Omega Λ, by rw [mul_neg, Omega_mul_Omega, neg_neg], hΩ⟩, rfl⟩
  have hKt : Kᵀ = Omega Λ * (-K) * (Omega Λ)⁻¹ := by
    have h : Kᵀ * Omega Λ = -(Omega Λ * K) := eq_neg_of_add_eq_zero_left hK
    calc Kᵀ = Kᵀ * Omega Λ * -Omega Λ := by
          rw [mul_assoc, mul_neg, Omega_mul_Omega, neg_neg, mul_one]
      _ = Omega Λ * (-K) * (Omega Λ)⁻¹ := by
        rw [h, hinv]; simp only [neg_mul, mul_neg, neg_neg]
  have hT : (flow K t)ᵀ = Omega Λ * flow K (-t) * (Omega Λ)⁻¹ := by
    unfold flow
    rw [← Matrix.exp_transpose, Matrix.transpose_smul, hKt, ← Matrix.exp_conj _ _ hU]
    congr 1
    simp only [Matrix.mul_smul, Matrix.smul_mul, neg_smul, smul_neg, mul_neg, neg_mul]
  rw [hT, hinv]
  calc Omega Λ * flow K (-t) * -Omega Λ * Omega Λ * flow K t
        = Omega Λ * (flow K (-t) * (-Omega Λ * Omega Λ) * flow K t) := by
          simp only [mul_assoc]
    _ = Omega Λ := by rw [hΩ, mul_one, flow_neg_mul_flow, mul_one]

/-- `σ(T_t u, T_t v) = σ(u, v)`. -/
theorem IsQuadraticGenerator.sigma_flow {K : Matrix (Λ × Fin 2) (Λ × Fin 2) ℝ}
    (hK : IsQuadraticGenerator K) (t : ℝ) (u v : Phase Λ) :
    sigma Λ (flow K t *ᵥ u) (flow K t *ᵥ v) = sigma Λ u v := by
  rw [sigma, Matrix.toBilin'_apply', Matrix.toBilin'_apply', Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec (flow K t *ᵥ u), ← Matrix.vecMul_transpose,
    Matrix.vecMul_vecMul, ← Matrix.dotProduct_mulVec, ← mul_assoc, hK.flow_symplectic]

/-- The flow as a linear equivalence of the phase space. -/
noncomputable def flowEquiv (K : Matrix (Λ × Fin 2) (Λ × Fin 2) ℝ) (t : ℝ) :
    Phase Λ ≃ₗ[ℝ] Phase Λ :=
  LinearEquiv.ofLinearMap (Matrix.toLin' (flow K t)) (Matrix.toLin' (flow K (-t)))
    (by rw [← Matrix.toLin'_mul, flow_mul_flow_neg, Matrix.toLin'_one])
    (by rw [← Matrix.toLin'_mul, flow_neg_mul_flow, Matrix.toLin'_one])

@[simp] theorem flowEquiv_apply (K : Matrix (Λ × Fin 2) (Λ × Fin 2) ℝ) (t : ℝ) (u : Phase Λ) :
    flowEquiv K t u = flow K t *ᵥ u :=
  Matrix.toLin'_apply _ _

/-- M5, Definition 2.4: the dynamics `α_t`, the automorphism of the CCR algebra induced by the
symplectic flow (BosonicLean's `CCR.relabel`). -/
noncomputable def alpha {K : Matrix (Λ × Fin 2) (Λ × Fin 2) ℝ} (hK : IsQuadraticGenerator K)
    (t : ℝ) : CCR (sigma Λ) ≃⋆ₐ[ℂ] CCR (sigma Λ) :=
  CCR.relabel (T := flowEquiv K t) fun u v => by
    rw [flowEquiv_apply, flowEquiv_apply]; exact hK.sigma_flow t u v

/-- `α_t(W f) = W(T_t f)`. -/
theorem alpha_wCCR {K : Matrix (Λ × Fin 2) (Λ × Fin 2) ℝ} (hK : IsQuadraticGenerator K)
    (t : ℝ) (f : Phase Λ) : alpha hK t (wCCR (sigma Λ) f) = wCCR (sigma Λ) (flow K t *ᵥ f) := by
  unfold alpha wCCR
  rw [CCR.relabel_weyl]
  exact Subtype.ext (congrArg (weyl (sigma Λ)) (flowEquiv_apply K t f))

section WeylCommutator

/-- M5, Theorem 3.2: `[W f, W g] = (e^{-iσ(f,g)} - 1) W g W f`. -/
theorem comm_wCCR_eq (f g : Phase Λ) :
    comm (wCCR (sigma Λ) f) (wCCR (sigma Λ) g) =
      (Complex.exp (((-(sigma Λ f g) : ℝ) : ℂ) * Complex.I) - 1) •
        (wCCR (sigma Λ) g * wCCR (sigma Λ) f) := by
  have h := (CCR.weylSystem (sigma Λ) sigma_isAlt).mul_comm_phase sigma_isAlt f g
  change wCCR (sigma Λ) f * wCCR (sigma Λ) g = _ • (wCCR (sigma Λ) g * wCCR (sigma Λ) f) at h
  rw [comm_def, h, sub_smul, one_smul]

/-- M5, Theorem 3.2: `‖[W f, W g]‖ = |e^{-iσ(f,g)} - 1|`. -/
theorem norm_comm_wCCR_eq (f g : Phase Λ) :
    ‖comm (wCCR (sigma Λ) f) (wCCR (sigma Λ) g)‖ =
      ‖Complex.exp (((-(sigma Λ f g) : ℝ) : ℂ) * Complex.I) - 1‖ := by
  have hU : wCCR (sigma Λ) g * wCCR (sigma Λ) f ∈ unitary (CCR (sigma Λ)) :=
    mul_mem ((CCR.weylSystem (sigma Λ) sigma_isAlt).mem_unitary g)
      ((CCR.weylSystem (sigma Λ) sigma_isAlt).mem_unitary f)
  rw [comm_wCCR_eq, norm_smul, CStarRing.norm_of_mem_unitary hU, mul_one]

/-- M5, Theorem 3.2: `‖[W f, W g]‖ = 2 |sin(σ(f,g)/2)|`. -/
theorem norm_comm_wCCR_eq_sin (f g : Phase Λ) :
    ‖comm (wCCR (sigma Λ) f) (wCCR (sigma Λ) g)‖ = 2 * |Real.sin (sigma Λ f g / 2)| := by
  rw [norm_comm_wCCR_eq, mul_comm (((-(sigma Λ f g) : ℝ) : ℂ)) Complex.I,
    Complex.norm_exp_I_mul_ofReal_sub_one]
  simp [neg_div, Real.sin_neg]

/-- M5, Theorem 3.2: `‖[W f, W g]‖ ≤ |σ(f, g)|`. -/
theorem norm_comm_wCCR_le (f g : Phase Λ) :
    ‖comm (wCCR (sigma Λ) f) (wCCR (sigma Λ) g)‖ ≤ |sigma Λ f g| := by
  rw [norm_comm_wCCR_eq, mul_comm (((-(sigma Λ f g) : ℝ) : ℂ)) Complex.I]
  calc _ ≤ ‖(-(sigma Λ f g) : ℝ)‖ := Real.norm_exp_I_mul_ofReal_sub_one_le
    _ = |sigma Λ f g| := by rw [Real.norm_eq_abs, abs_neg]

end WeylCommutator

section Bound

/-- The coordinates of the sites of a region. -/
def coords (X : Finset Λ) : Finset (Λ × Fin 2) := Finset.univ.filter fun b => b.1 ∈ X

/-- `|σ(u, g)| ≤ ∑_b |u_b| |g_{b̄}|`. -/
theorem abs_sigma_le (u g : Phase Λ) : |sigma Λ u g| ≤ ∑ b, |u b| * |g (conj b)| := by
  rw [sigma_apply, Fintype.sum_prod_type]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun x _ => ?_)
  simp only [Fin.sum_univ_two, conj, Fin.isValue, ite_true, one_ne_zero, ite_false]
  rw [← abs_mul, ← abs_mul]
  exact abs_sub _ _

/-- `|(T_t f)_b| ≤ ∑_{a ∈ X'} (e^{|t||K|})_{ba} |f_a|` for `f` supported in `X`. -/
theorem abs_flow_mulVec_apply_le (K : Matrix (Λ × Fin 2) (Λ × Fin 2) ℝ) (t : ℝ)
    {f : Phase Λ} {X : Finset Λ} (hf : SuppIn f X) (b : Λ × Fin 2) :
    |(flow K t *ᵥ f) b| ≤ ∑ a ∈ coords X, NormedSpace.exp (|t| • absEntry K) b a * |f a| := by
  have h1 : (flow K t *ᵥ f) b = ∑ a ∈ coords X, flow K t b a * f a := by
    rw [Matrix.mulVec, dotProduct]
    refine (Finset.sum_subset (Finset.subset_univ _) fun a _ ha => ?_).symm
    rw [hf.apply_eq_zero (by simpa [coords] using ha), mul_zero]
  rw [h1]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun a _ => ?_)
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_right (abs_exp_apply_le K t b a) (abs_nonneg _)

/-- M5, Theorem 6.1: the harmonic Lieb-Robinson bound. -/
theorem liebRobinson_weyl {K : Matrix (Λ × Fin 2) (Λ × Fin 2) ℝ} (hK : IsQuadraticGenerator K)
    (t : ℝ) {f g : Phase Λ} {X Y : Finset Λ} (hf : SuppIn f X) (hg : SuppIn g Y) :
    ‖comm (alpha hK t (wCCR (sigma Λ) f)) (wCCR (sigma Λ) g)‖ ≤ |sigma Λ (flow K t *ᵥ f) g| ∧
    |sigma Λ (flow K t *ᵥ f) g| ≤
      ∑ b ∈ coords Y, ∑ a ∈ coords X,
        NormedSpace.exp (|t| • absEntry K) b a * |f a| * |g (conj b)| := by
  refine ⟨?_, (abs_sigma_le _ _).trans ?_⟩
  · rw [alpha_wCCR]
    exact norm_comm_wCCR_le _ _
  · rw [← Finset.sum_subset (Finset.subset_univ (coords Y)) fun b _ hb => by
      rw [hg.apply_eq_zero (b := conj b) (by simpa [coords, conj] using hb), abs_zero, mul_zero]]
    refine Finset.sum_le_sum fun b _ => ?_
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right (abs_flow_mulVec_apply_le K t hf b) (abs_nonneg _)

/-- The harmonic bound with every entry `(e^{t|K|})_{ba}`, `b ∈ Y'`, `a ∈ X'`, at most `C`. -/
private theorem liebRobinson_weyl_of_le {K : Matrix (Λ × Fin 2) (Λ × Fin 2) ℝ}
    (hK : IsQuadraticGenerator K) {t : ℝ} (ht : 0 ≤ t) {f g : Phase Λ} {X Y : Finset Λ}
    (hf : SuppIn f X) (hg : SuppIn g Y) {C : ℝ}
    (hC : ∀ y ∈ Y, ∀ x ∈ X, ∀ b a : Λ × Fin 2, b.1 = y → a.1 = x →
      NormedSpace.exp (t • absEntry K) b a ≤ C) :
    ‖comm (alpha hK t (wCCR (sigma Λ) f)) (wCCR (sigma Λ) g)‖ ≤
      (∑ a, |f a|) * (∑ b, |g b|) * C := by
  obtain ⟨h1, h2⟩ := liebRobinson_weyl hK t hf hg
  refine h1.trans (h2.trans ?_)
  rw [abs_of_nonneg ht]
  have hfX : ∀ a ∉ coords X, |f a| = 0 := fun a ha => by
    rw [hf.apply_eq_zero (by simpa [coords] using ha), abs_zero]
  have hgY : ∀ b ∉ coords Y, |g (conj b)| = 0 := fun b hb => by
    rw [hg.apply_eq_zero (b := conj b) (by simpa [coords, conj] using hb), abs_zero]
  have hconj : ∑ b, |g (conj b)| = ∑ b, |g b| := by
    simp only [Fintype.sum_prod_type, Fin.sum_univ_two, conj, Fin.isValue, ite_true,
      one_ne_zero, ite_false, add_comm]
  calc ∑ b ∈ coords Y, ∑ a ∈ coords X,
        NormedSpace.exp (t • absEntry K) b a * |f a| * |g (conj b)|
      ≤ ∑ b ∈ coords Y, ∑ a ∈ coords X, C * |f a| * |g (conj b)| := by
        refine Finset.sum_le_sum fun b hb => Finset.sum_le_sum fun a ha => ?_
        have hb' : b.1 ∈ Y := by simpa [coords] using hb
        have ha' : a.1 ∈ X := by simpa [coords] using ha
        gcongr
        exact hC _ hb' _ ha' b a rfl rfl
    _ = ∑ b, ∑ a, C * |f a| * |g (conj b)| := by
        rw [← Finset.sum_subset (Finset.subset_univ (coords Y)) fun b _ hb => by
          simp [hgY b hb]]
        refine Finset.sum_congr rfl fun b _ => ?_
        exact Finset.sum_subset (Finset.subset_univ _) fun a _ ha => by simp [hfX a ha]
    _ = (∑ a, |f a|) * (∑ b, |g b|) * C := by
        rw [← hconj, mul_comm (∑ a, |f a|), Finset.sum_mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun a _ => by ring

/-- M5, Corollary 6.2 (range form): with range `R` and row sum `v` of `K` for a distance `d` on
the sites, and `n R < d(y, x)` for all `y ∈ Y`, `x ∈ X`, `n < r`,
`‖[α_t(W f), W g]‖ ≤ ‖f‖₁ ‖g‖₁ (vt)^r/r! e^{vt}` for `t ≥ 0`. -/
theorem liebRobinson_weyl_geom {K : Matrix (Λ × Fin 2) (Λ × Fin 2) ℝ}
    (hK : IsQuadraticGenerator K) {d : Λ → Λ → ℝ} (hd0 : ∀ x, d x x = 0)
    (hd : ∀ x y z, d x z ≤ d x y + d y z) {R v : ℝ} (hR : HasRange K Prod.fst d R)
    (hv : RowSumLE K v) (hv0 : 0 ≤ v) {t : ℝ} (ht : 0 ≤ t) {f g : Phase Λ} {X Y : Finset Λ}
    (hf : SuppIn f X) (hg : SuppIn g Y) {r : ℕ}
    (hr : ∀ y ∈ Y, ∀ x ∈ X, ∀ n < r, n * R < d y x) :
    ‖comm (alpha hK t (wCCR (sigma Λ) f)) (wCCR (sigma Λ) g)‖ ≤
      (∑ a, |f a|) * (∑ b, |g b|) * ((v * t) ^ r / (r.factorial : ℝ) * Real.exp (v * t)) :=
  liebRobinson_weyl_of_le hK ht hf hg fun y hy x hx b a hb ha =>
    exp_absEntry_apply_le_geom hd0 hd hR hv hv0 ht fun n hn => by
      rw [hb, ha]; exact hr y hy x hx n hn

/-- M5, Corollary 6.2 (light cone): for `μ ≥ 0` and `r ≥ 1`,
`‖[α_t(W f), W g]‖ ≤ ‖f‖₁ ‖g‖₁ e^{-μ r} (e^{e^μ v t} - 1)`. -/
theorem liebRobinson_weyl_cone {K : Matrix (Λ × Fin 2) (Λ × Fin 2) ℝ}
    (hK : IsQuadraticGenerator K) {d : Λ → Λ → ℝ} (hd0 : ∀ x, d x x = 0)
    (hd : ∀ x y z, d x z ≤ d x y + d y z) {R v : ℝ} (hR : HasRange K Prod.fst d R)
    (hv : RowSumLE K v) (hv0 : 0 ≤ v) {t : ℝ} (ht : 0 ≤ t) {μ : ℝ} (hμ : 0 ≤ μ)
    {f g : Phase Λ} {X Y : Finset Λ} (hf : SuppIn f X) (hg : SuppIn g Y) {r : ℕ} (hr1 : 1 ≤ r)
    (hr : ∀ y ∈ Y, ∀ x ∈ X, ∀ n < r, n * R < d y x) :
    ‖comm (alpha hK t (wCCR (sigma Λ) f)) (wCCR (sigma Λ) g)‖ ≤
      (∑ a, |f a|) * (∑ b, |g b|) *
        (Real.exp (-μ * r) * (Real.exp (Real.exp μ * (v * t)) - 1)) :=
  liebRobinson_weyl_of_le hK ht hf hg fun y hy x hx b a hb ha =>
    exp_absEntry_apply_le_cone hd0 hd hR hv hv0 ht hμ hr1 fun n hn => by
      rw [hb, ha]; exact hr y hy x hx n hn

end Bound

end LocalityLean.Bosonic
