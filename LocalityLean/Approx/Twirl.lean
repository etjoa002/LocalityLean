/-
Copyright (c) 2026 LocalityLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LocalityLean contributors
-/
import LocalityLean.Qudit.Config
import LocalityLean.Approx.LocalApprox
import LocalityLean.Core.Derivation
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# The conditional expectation on the qudit net

For any finite alphabets, the conditional expectation `condExp X M` onto the local algebra of a
region `X` is the normalized partial trace over the complement, re-embedded:
`(E_X M) s s' = [s ~_X s'] · |Ω_{Xᶜ}|⁻¹ Σ_η M (s|X, η) (s'|X, η)` (M3, Definition 2.2). It is a
projection onto `𝒜(X)`, linear, unital and star-preserving.

For cyclic alphabets `ZMod (q u)` (one `q u ≥ 1` per site) it is also the finite *twirl*: the
average of `U M U^*` over the Weyl unitaries `U_{α,β}` of the complement, the matrices
`(U_{α,β}) s s' = [s = s' + α] ∏_{u ∉ X} χ_u(β u · s' u)` with `χ_u` the additive character
`k ↦ e^{2πik/q_u}` (M3, Definition 2.1 and Proposition 3.3). The twirl form gives the
contraction `‖E_X M‖ ≤ ‖M‖`, the bimodule property and the local-approximation estimate
`‖M - E_X M‖ ≤ N_{Xᶜ}(M)` (M3, Theorem 3.5); the converse `N_{Xᶜ}(M) ≤ 2 ‖M - E_X M‖` is the
general `commNorm_le_two_mul_norm_sub`. Together they make the qudit net a net with local
approximation, `localApprox`.

The single-site clock and shift matrices and their relation `ZX = χ(1) XZ` are recorded
(M3, Proposition 3.1).

## Main definitions

* `LocalityLean.Qudit.condExp`, `LocalityLean.Qudit.chi`, `LocalityLean.Qudit.weyl`,
  `LocalityLean.Qudit.twirl`, `LocalityLean.Qudit.localApprox`.

## Main statements

* `LocalityLean.Qudit.isLocal_condExp`, `condExp_of_isLocal`, `condExp_condExp`,
  `condExp_one`, `star_condExp`, `condExp_univ`, `condExp_empty`;
* `LocalityLean.Qudit.charSum`, `isLocal_weyl`, `weyl_mem_unitary`, `weyl_conj_apply`,
  `twirl_eq_condExp`, `norm_condExp_le`, `condExp_mul_left`, `condExp_mul_right`,
  `norm_sub_condExp_le_commNorm`, `commNorm_compl_le_two_mul_norm_sub_condExp`.
-/

noncomputable section

namespace LocalityLean.Qudit

open LinearAQFT

/-! ### The conditional expectation for any finite alphabets (M3, Definition 2.2) -/

section CondExp

variable {Λ : Type*} {σ : Λ → Type*}

/-- `glue Xᶜ η s` depends on `s` through `s|X` only. -/
theorem glue_compl_eq_of_restrict_eq (X : Set Λ) (η : (y : (Xᶜ : Set Λ)) → σ y)
    {s r : Config σ} (h : restrict X s = restrict X r) : glue Xᶜ η s = glue Xᶜ η r := by
  funext u
  by_cases hu : u ∈ X
  · have hu' : u ∉ Xᶜ := fun h' => h' hu
    simp only [glue, hu', dite_false]
    exact congrFun h ⟨u, hu⟩
  · have hu' : u ∈ Xᶜ := hu
    simp [glue, hu']

theorem glue_compl_agreesOff (X : Set Λ) (η : (y : (Xᶜ : Set Λ)) → σ y) (s s' : Config σ) :
    AgreesOff X (glue Xᶜ η s) (glue Xᶜ η s') := by
  intro u hu
  have hu' : u ∈ Xᶜ := hu
  simp [glue, hu']

theorem restrict_glue_compl (X : Set Λ) (η : (y : (Xᶜ : Set Λ)) → σ y) (s : Config σ) :
    restrict X (glue Xᶜ η s) = restrict X s := by
  funext ⟨u, hu⟩
  have hu' : u ∉ Xᶜ := fun h' => h' hu
  simp [restrict, glue, hu']

variable [Fintype Λ] [DecidableEq Λ] [∀ u, Fintype (σ u)]

open Classical in
/-- The conditional expectation onto `X`: the normalized partial trace over the complement,
re-embedded. -/
def condExp (X : Set Λ) (M : QuditAlgebra σ) : QuditAlgebra σ :=
  Matrix.of fun s s' => if AgreesOff X s s' then
    (Fintype.card ((y : (Xᶜ : Set Λ)) → σ y) : ℂ)⁻¹ *
      ∑ η : (y : (Xᶜ : Set Λ)) → σ y, M (glue Xᶜ η s) (glue Xᶜ η s') else 0

open Classical in
theorem condExp_apply (X : Set Λ) (M : QuditAlgebra σ) (s s' : Config σ) :
    condExp X M s s' = if AgreesOff X s s' then
      (Fintype.card ((y : (Xᶜ : Set Λ)) → σ y) : ℂ)⁻¹ *
        ∑ η : (y : (Xᶜ : Set Λ)) → σ y, M (glue Xᶜ η s) (glue Xᶜ η s') else 0 := rfl

/-- M3, Proposition 3.4 (a): the conditional expectation is local to `X`. -/
theorem isLocal_condExp (X : Set Λ) (M : QuditAlgebra σ) : IsLocal X (condExp X M) := by
  classical
  constructor
  · intro s s' h
    simp [condExp_apply, h]
  · intro s s' r r' hs hr h1 h2
    simp only [condExp_apply, hs, hr, ite_true]
    congr 1
    refine Finset.sum_congr rfl fun η _ => ?_
    rw [glue_compl_eq_of_restrict_eq X η h1, glue_compl_eq_of_restrict_eq X η h2]

/-- M3, Proposition 3.4 (a): the conditional expectation fixes the matrices local to `X`. -/
theorem condExp_of_isLocal [∀ u, Nonempty (σ u)] {X : Set Λ} {M : QuditAlgebra σ}
    (hM : IsLocal X M) : condExp X M = M := by
  classical
  ext s s'
  rw [condExp_apply]
  split_ifs with h
  · have : ∀ η : (y : (Xᶜ : Set Λ)) → σ y, M (glue Xᶜ η s) (glue Xᶜ η s') = M s s' := fun η =>
      hM.2 _ _ _ _ (glue_compl_agreesOff X η s s') h (restrict_glue_compl X η s)
        (restrict_glue_compl X η s')
    simp only [this, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [← mul_assoc, inv_mul_cancel₀, one_mul]
    exact_mod_cast Fintype.card_ne_zero
  · exact (hM.1 s s' h).symm

theorem condExp_condExp [∀ u, Nonempty (σ u)] (X : Set Λ) (M : QuditAlgebra σ) :
    condExp X (condExp X M) = condExp X M :=
  condExp_of_isLocal (isLocal_condExp X M)

theorem condExp_add (X : Set Λ) (M N : QuditAlgebra σ) :
    condExp X (M + N) = condExp X M + condExp X N := by
  classical
  ext s s'
  simp only [condExp_apply, Matrix.add_apply]
  split_ifs <;> simp [Finset.sum_add_distrib, mul_add]

theorem condExp_sub (X : Set Λ) (M N : QuditAlgebra σ) :
    condExp X (M - N) = condExp X M - condExp X N := by
  classical
  ext s s'
  simp only [condExp_apply, Matrix.sub_apply]
  split_ifs <;> simp [Finset.sum_sub_distrib, mul_sub]

theorem condExp_smul (X : Set Λ) (c : ℂ) (M : QuditAlgebra σ) :
    condExp X (c • M) = c • condExp X M := by
  classical
  ext s s'
  simp only [condExp_apply, Matrix.smul_apply, smul_eq_mul]
  split_ifs
  · rw [← Finset.mul_sum, mul_left_comm]
  · simp

theorem condExp_zero (X : Set Λ) : condExp X (0 : QuditAlgebra σ) = 0 := by
  classical
  ext s s'
  simp [condExp_apply]

/-- M3, Proposition 3.4 (b): the conditional expectation commutes with the adjoint. -/
theorem star_condExp (X : Set Λ) (M : QuditAlgebra σ) :
    star (condExp X M) = condExp X (star M) := by
  classical
  ext s s'
  rw [Matrix.star_apply, condExp_apply, condExp_apply]
  by_cases h : AgreesOff X s s'
  · rw [ite_eq_left h.symm, ite_eq_left h, star_mul', star_sum, star_inv₀, star_natCast]
    simp only [Matrix.star_apply]
  · have h' : ¬ AgreesOff X s' s := fun h' => h h'.symm
    simp [h, h']

theorem condExp_one [∀ u, DecidableEq (σ u)] [∀ u, Nonempty (σ u)] (X : Set Λ) :
    condExp X (1 : QuditAlgebra σ) = 1 :=
  condExp_of_isLocal (isLocal_one X)

/-- M3, Proposition 3.4 (d): the conditional expectation onto the whole lattice is the
identity. -/
theorem condExp_univ [∀ u, Nonempty (σ u)] (M : QuditAlgebra σ) :
    condExp Set.univ M = M := by
  classical
  have : M ∈ localAlgebra (σ := σ) Set.univ := by
    rw [localAlgebra_univ]
    exact StarSubalgebra.mem_top
  exact condExp_of_isLocal this

/-- M3, Proposition 3.4 (d): the conditional expectation onto the empty region is the
normalized trace times the identity. -/
theorem condExp_empty [∀ u, DecidableEq (σ u)] (M : QuditAlgebra σ) :
    condExp ∅ M = ((Fintype.card (Config σ) : ℂ)⁻¹ * Matrix.trace M) • (1 : QuditAlgebra σ) := by
  classical
  ext s s'
  rw [condExp_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  have hiff : AgreesOff ∅ s s' ↔ s = s' :=
    ⟨fun h => funext fun u => h u (Set.notMem_empty u), fun h => h ▸ agreesOff_refl ∅ s⟩
  set e : ((y : ((∅ : Set Λ)ᶜ : Set Λ)) → σ y) → Config σ := fun η u => η ⟨u, by simp⟩ with he_def
  have he : Function.Bijective e :=
    ⟨fun η η' h => funext fun ⟨u, hu⟩ => congrFun h u, fun t => ⟨fun y => t y.1, rfl⟩⟩
  by_cases h : s = s'
  · subst h
    rw [ite_eq_left (agreesOff_refl ∅ s), ite_eq_left rfl, mul_one]
    have hsum : ∑ η : (y : ((∅ : Set Λ)ᶜ : Set Λ)) → σ y,
        M (glue (∅ : Set Λ)ᶜ η s) (glue (∅ : Set Λ)ᶜ η s) = Matrix.trace M := by
      rw [Matrix.trace]
      refine Fintype.sum_bijective e he _ _ fun η => ?_
      have : glue (∅ : Set Λ)ᶜ η s = e η := by
        funext u
        simp [glue, he_def]
      rw [this, Matrix.diag_apply]
    have hcard : (Fintype.card ((y : ((∅ : Set Λ)ᶜ : Set Λ)) → σ y) : ℂ) =
        Fintype.card (Config σ) := by
      exact_mod_cast Fintype.card_of_bijective he
    have key : (Fintype.card ((y : ((∅ : Set Λ)ᶜ : Set Λ)) → σ y) : ℂ)⁻¹ *
        ∑ η : (y : ((∅ : Set Λ)ᶜ : Set Λ)) → σ y,
          M (glue (∅ : Set Λ)ᶜ η s) (glue (∅ : Set Λ)ᶜ η s) =
        (Fintype.card (Config σ) : ℂ)⁻¹ * Matrix.trace M := by
      rw [hsum, hcard]
    convert key using 3
    all_goals first
      | exact congrArg (@Finset.univ _) (Subsingleton.elim _ _)
      | exact congrArg (Nat.cast (R := ℂ)) (congrArg (@Fintype.card _) (Subsingleton.elim _ _))
  · rw [ite_eq_right (fun h' => h (hiff.1 h')), ite_eq_right h, mul_zero]

section Net

variable [∀ u, DecidableEq (σ u)]

theorem condExp_mem (X : Set Λ) (M : QuditAlgebra σ) : condExp X M ∈ localAlgebra X :=
  isLocal_condExp X M

end Net

end CondExp

/-! ### Characters, clock and shift on a cyclic alphabet (M3, Proposition 3.1) -/

section Cyclic

/-- The primitive root `e^{2πi/n}`. -/
def omega (n : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / n)

theorem omega_isPrimitiveRoot (n : ℕ) [NeZero n] : IsPrimitiveRoot (omega n) n :=
  Complex.isPrimitiveRoot_exp n (NeZero.ne n)

theorem omega_pow (n : ℕ) [NeZero n] : omega n ^ n = 1 := (omega_isPrimitiveRoot n).pow_eq_one

/-- The additive character `k ↦ e^{2πik/n}` of `ZMod n`. -/
def chi (n : ℕ) [NeZero n] : AddChar (ZMod n) ℂ := AddChar.zmodChar n (omega_pow n)

variable {n : ℕ} [NeZero n]

theorem chi_apply (k : ZMod n) : chi n k = omega n ^ k.val := rfl

theorem chi_isPrimitive : (chi n).IsPrimitive :=
  AddChar.zmodChar_primitive_of_primitive_root n (omega_isPrimitiveRoot n)

theorem chi_add (k k' : ZMod n) : chi n (k + k') = chi n k * chi n k' :=
  AddChar.map_add_eq_mul (chi n) k k'

theorem chi_zero : chi n 0 = 1 := AddChar.map_zero_eq_one (chi n)

theorem chi_pow_card (k : ZMod n) : chi n k ^ n = 1 := by
  rw [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul, ZMod.natCast_self, zero_mul, chi_zero]

theorem norm_chi (k : ZMod n) : ‖chi n k‖ = 1 :=
  Complex.norm_eq_one_of_pow_eq_one (chi_pow_card k) (NeZero.ne n)

theorem star_chi (k : ZMod n) : star (chi n k) = chi n (-k) := by
  rw [AddChar.map_neg_eq_inv, Complex.star_def]
  exact eq_inv_of_mul_eq_one_right (by simp [Complex.mul_conj'])

/-- M3, Proposition 3.1, the character sum: `Σ_b χ(b k) = n [k = 0]`. -/
theorem charSum (k : ZMod n) :
    ∑ b : ZMod n, chi n (b * k) = if k = 0 then (n : ℂ) else 0 := by
  have h := AddChar.sum_mulShift (ψ := chi n) k chi_isPrimitive
  simpa [ZMod.card] using h

/-- The clock matrix `Z_{kk'} = χ(k) [k = k']`. -/
def clock (n : ℕ) [NeZero n] : Matrix (ZMod n) (ZMod n) ℂ :=
  Matrix.diagonal fun k => chi n k

/-- The shift matrix `X_{kk'} = [k = k' + 1]`. -/
def shift (n : ℕ) [NeZero n] : Matrix (ZMod n) (ZMod n) ℂ :=
  Matrix.of fun k k' => if k = k' + 1 then 1 else 0

/-- M3, Proposition 3.1: `ZX = χ(1) XZ`. -/
theorem clock_mul_shift : clock n * shift n = chi n 1 • (shift n * clock n) := by
  ext k k'
  simp only [clock, shift, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.of_apply,
    Matrix.smul_apply, smul_eq_mul]
  split_ifs with h
  · subst h
    rw [chi_add]; ring
  · simp

/-- The shift is unitary: `X X^* = 1`. -/
theorem shift_mul_star : shift n * star (shift n) = 1 := by
  ext k k'
  simp only [Matrix.mul_apply, Matrix.star_apply, shift, Matrix.of_apply, Matrix.one_apply]
  rw [Finset.sum_eq_single (k - 1)]
  · simp only [sub_add_cancel, ite_true, one_mul]
    by_cases hk : k = k'
    · subst hk; simp
    · have : k' ≠ k - 1 + 1 := by rw [sub_add_cancel]; exact Ne.symm hk
      have hk' : k' ≠ k := Ne.symm hk
      simp [hk, hk']
  · intro j _ hj
    have : k ≠ j + 1 := fun h => hj (by rw [h]; ring)
    simp [this]
  · intro h; exact absurd (Finset.mem_univ _) h

end Cyclic

/-! ### Weyl unitaries and the twirl (M3, Definitions 2.1-2.2, Propositions 3.2-3.5) -/

section Weyl

variable {Λ : Type*} {q : Λ → ℕ}

open Classical in
/-- The configuration shifted by the letters `α` on `Y`: `s u + α u` on `Y`, `s u` off `Y`. -/
def shiftBy (Y : Set Λ) (α : (y : Y) → ZMod (q y)) (s : Config fun u => ZMod (q u)) :
    Config fun u => ZMod (q u) :=
  glue Y (restrict Y s + α) s

variable (Y : Set Λ)

theorem shiftBy_agreesOff (α : (y : Y) → ZMod (q y)) (s : Config fun u => ZMod (q u)) :
    AgreesOff Y (shiftBy Y α s) s :=
  glue_agreesOff Y _ s

theorem restrict_shiftBy (α : (y : Y) → ZMod (q y)) (s : Config fun u => ZMod (q u)) :
    restrict Y (shiftBy Y α s) = restrict Y s + α :=
  restrict_glue Y _ s

theorem shiftBy_apply_of_mem (α : (y : Y) → ZMod (q y)) (s : Config fun u => ZMod (q u))
    {u : Λ} (hu : u ∈ Y) : shiftBy Y α s u = s u + α ⟨u, hu⟩ := by
  simp [shiftBy, glue, hu, restrict]

theorem shiftBy_apply_of_not_mem (α : (y : Y) → ZMod (q y)) (s : Config fun u => ZMod (q u))
    {u : Λ} (hu : u ∉ Y) : shiftBy Y α s u = s u := by
  simp [shiftBy, glue, hu]

theorem shiftBy_zero (s : Config fun u => ZMod (q u)) : shiftBy Y 0 s = s := by
  rw [shiftBy, add_zero, glue_restrict (agreesOff_refl Y s)]

theorem shiftBy_shiftBy (α α' : (y : Y) → ZMod (q y)) (s : Config fun u => ZMod (q u)) :
    shiftBy Y α (shiftBy Y α' s) = shiftBy Y (α' + α) s := by
  funext u
  by_cases hu : u ∈ Y
  · simp [shiftBy_apply_of_mem Y _ _ hu, add_assoc]
  · simp [shiftBy_apply_of_not_mem Y _ _ hu]

theorem shiftBy_neg_shiftBy (α : (y : Y) → ZMod (q y)) (s : Config fun u => ZMod (q u)) :
    shiftBy Y (-α) (shiftBy Y α s) = s := by
  rw [shiftBy_shiftBy, add_neg_cancel, shiftBy_zero]

theorem shiftBy_shiftBy_neg (α : (y : Y) → ZMod (q y)) (s : Config fun u => ZMod (q u)) :
    shiftBy Y α (shiftBy Y (-α) s) = s := by
  rw [shiftBy_shiftBy, neg_add_cancel, shiftBy_zero]

theorem shiftBy_injective (α : (y : Y) → ZMod (q y)) : Function.Injective (shiftBy Y α) :=
  fun s s' h => by
    rw [← shiftBy_neg_shiftBy Y α s, h, shiftBy_neg_shiftBy]

theorem eq_shiftBy_iff (α : (y : Y) → ZMod (q y)) {s s' : Config fun u => ZMod (q u)}
    (h : AgreesOff Y s s') : s = shiftBy Y α s' ↔ restrict Y s = restrict Y s' + α := by
  rw [eq_iff_restrict_eq (h.trans (shiftBy_agreesOff Y α s').symm), restrict_shiftBy]

variable [∀ u, NeZero (q u)] [Fintype Y]

/-- The phase `∏_{y ∈ Y} χ_y(β y · s y)`. -/
def phase (β : (y : Y) → ZMod (q y)) (s : Config fun u => ZMod (q u)) : ℂ :=
  ∏ y : Y, chi (q y) (β y * s y)

theorem phase_eq_of_restrict_eq (β : (y : Y) → ZMod (q y)) {s s' : Config fun u => ZMod (q u)}
    (h : restrict Y s = restrict Y s') : phase Y β s = phase Y β s' := by
  classical
  unfold phase
  refine Finset.prod_congr rfl fun y _ => ?_
  rw [show s y = s' y from congrFun h y]

theorem phase_add_left (β β' : (y : Y) → ZMod (q y)) (s : Config fun u => ZMod (q u)) :
    phase Y (β + β') s = phase Y β s * phase Y β' s := by
  classical
  unfold phase
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun y _ => ?_
  rw [Pi.add_apply, add_mul, chi_add]

theorem phase_add_right (β : (y : Y) → ZMod (q y)) (s s' : Config fun u => ZMod (q u)) :
    phase Y β (s + s') = phase Y β s * phase Y β s' := by
  classical
  unfold phase
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun y _ => ?_
  rw [Pi.add_apply, mul_add, chi_add]

theorem phase_zero_right (β : (y : Y) → ZMod (q y)) : phase Y β 0 = 1 := by
  classical
  simp [phase]

theorem star_phase (β : (y : Y) → ZMod (q y)) (s : Config fun u => ZMod (q u)) :
    star (phase Y β s) = phase Y β (-s) := by
  classical
  unfold phase
  rw [star_prod]
  refine Finset.prod_congr rfl fun y _ => ?_
  rw [star_chi, Pi.neg_apply, mul_neg]

theorem phase_mul_star_phase_self (β : (y : Y) → ZMod (q y))
    (s : Config fun u => ZMod (q u)) : phase Y β s * star (phase Y β s) = 1 := by
  rw [star_phase, ← phase_add_right, add_neg_cancel, phase_zero_right]

/-- The phases of two configurations shifted by the same letters: `α` cancels. -/
theorem phase_shiftBy_mul_star (α β : (y : Y) → ZMod (q y))
    (s s' : Config fun u => ZMod (q u)) :
    phase Y β (shiftBy Y α s) * star (phase Y β (shiftBy Y α s')) = phase Y β (s - s') := by
  rw [star_phase, ← phase_add_right]
  apply phase_eq_of_restrict_eq
  funext y
  simp only [restrict, Pi.add_apply, Pi.neg_apply, Pi.sub_apply,
    shiftBy_apply_of_mem Y _ _ y.2]
  abel

open Classical in
/-- M3, Definition 2.1: the Weyl unitary `U_{α,β}` of the letters `α, β` on `Y`,
`(U_{α,β}) s s' = [s = s' + α] ∏_{y ∈ Y} χ_y(β y · s' y)`. -/
def weyl (α β : (y : Y) → ZMod (q y)) : QuditAlgebra fun u => ZMod (q u) :=
  Matrix.of fun s s' => if s = shiftBy Y α s' then phase Y β s' else 0

open Classical in
theorem weyl_apply (α β : (y : Y) → ZMod (q y)) (s s' : Config fun u => ZMod (q u)) :
    weyl Y α β s s' = if s = shiftBy Y α s' then phase Y β s' else 0 := rfl

/-- M3, Proposition 3.2: the Weyl unitaries are local to `Y`. -/
theorem isLocal_weyl (α β : (y : Y) → ZMod (q y)) : IsLocal Y (weyl Y α β) := by
  classical
  constructor
  · intro s s' h
    have : s ≠ shiftBy Y α s' := fun e => h (by rw [e]; exact shiftBy_agreesOff Y α s')
    simp [weyl_apply, this]
  · intro s s' r r' hs hr h1 h2
    simp only [weyl_apply]
    rw [phase_eq_of_restrict_eq Y β h2]
    have : (s = shiftBy Y α s') ↔ (r = shiftBy Y α r') := by
      rw [eq_shiftBy_iff Y α hs, eq_shiftBy_iff Y α hr, h1, h2]
    by_cases e : s = shiftBy Y α s'
    · rw [ite_eq_left e, ite_eq_left (this.1 e)]
    · rw [ite_eq_right e, ite_eq_right (fun e' => e (this.2 e'))]

variable [Fintype Λ] [DecidableEq Λ]

theorem weyl_mem (α β : (y : Y) → ZMod (q y)) : weyl Y α β ∈ localAlgebra Y :=
  isLocal_weyl Y α β

theorem star_weyl_mul_weyl (α β : (y : Y) → ZMod (q y)) :
    star (weyl Y α β) * weyl Y α β = 1 := by
  classical
  ext s s'
  rw [Matrix.mul_apply, Matrix.one_apply]
  rw [Finset.sum_eq_single (shiftBy Y α s)]
  · rw [Matrix.star_apply, weyl_apply, weyl_apply, ite_eq_left rfl]
    by_cases h : s = s'
    · subst h
      rw [ite_eq_left rfl, ite_eq_left rfl, mul_comm, phase_mul_star_phase_self]
    · have : shiftBy Y α s ≠ shiftBy Y α s' := fun e => h (shiftBy_injective Y α e)
      rw [ite_eq_right this, ite_eq_right h, mul_zero]
  · intro r _ hr
    rw [Matrix.star_apply, weyl_apply, ite_eq_right hr, star_zero, zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem weyl_mul_star_weyl (α β : (y : Y) → ZMod (q y)) :
    weyl Y α β * star (weyl Y α β) = 1 := by
  classical
  ext s s'
  rw [Matrix.mul_apply, Matrix.one_apply]
  rw [Finset.sum_eq_single (shiftBy Y (-α) s)]
  · rw [Matrix.star_apply, weyl_apply, weyl_apply, ite_eq_left (shiftBy_shiftBy_neg Y α s).symm]
    by_cases h : s = s'
    · subst h
      rw [ite_eq_left (shiftBy_shiftBy_neg Y α s).symm, ite_eq_left rfl, phase_mul_star_phase_self]
    · have : s' ≠ shiftBy Y α (shiftBy Y (-α) s) := by
        rw [shiftBy_shiftBy_neg]; exact Ne.symm h
      rw [ite_eq_right this, ite_eq_right h, star_zero, mul_zero]
  · intro r _ hr
    have : s ≠ shiftBy Y α r := fun e => hr (by rw [e, shiftBy_neg_shiftBy])
    rw [weyl_apply, ite_eq_right this, zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- M3, Proposition 3.2: the Weyl unitaries are unitary. -/
theorem weyl_mem_unitary (α β : (y : Y) → ZMod (q y)) :
    weyl Y α β ∈ unitary (QuditAlgebra fun u => ZMod (q u)) :=
  Unitary.mem_iff.mpr ⟨star_weyl_mul_weyl Y α β, weyl_mul_star_weyl Y α β⟩

/-- M3, Proposition 3.2, the conjugation formula:
`(U M U^*) s s' = φ_β(s - α) φ_β(s' - α)^* M (s - α) (s' - α)`. -/
theorem weyl_conj_apply (α β : (y : Y) → ZMod (q y)) (M : QuditAlgebra fun u => ZMod (q u))
    (s s' : Config fun u => ZMod (q u)) :
    (weyl Y α β * M * star (weyl Y α β)) s s' =
      phase Y β (shiftBy Y (-α) s) * star (phase Y β (shiftBy Y (-α) s')) *
        M (shiftBy Y (-α) s) (shiftBy Y (-α) s') := by
  classical
  rw [Matrix.mul_apply, Finset.sum_eq_single (shiftBy Y (-α) s')]
  · rw [Matrix.mul_apply, Finset.sum_eq_single (shiftBy Y (-α) s)]
    · rw [Matrix.star_apply, weyl_apply, weyl_apply, ite_eq_left (shiftBy_shiftBy_neg Y α s).symm,
        ite_eq_left (shiftBy_shiftBy_neg Y α s').symm]
      ring
    · intro r _ hr
      have : s ≠ shiftBy Y α r := fun e => hr (by rw [e, shiftBy_neg_shiftBy])
      rw [weyl_apply, ite_eq_right this, zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro r _ hr
    have : s' ≠ shiftBy Y α r := fun e => hr (by rw [e, shiftBy_neg_shiftBy])
    rw [Matrix.star_apply, weyl_apply, ite_eq_right this, star_zero, mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

omit [Fintype Λ] in
/-- The character sum over the letters on `Y`: `Σ_β φ_β(d) = |Ω_Y| [d = 0 on Y]`. -/
theorem sum_phase (d : Config fun u => ZMod (q u)) :
    ∑ β : (y : Y) → ZMod (q y), phase Y β d =
      if (∀ y : Y, d y = 0) then (Fintype.card ((y : Y) → ZMod (q y)) : ℂ) else 0 := by
  classical
  simp only [phase]
  rw [show (∑ β : (y : Y) → ZMod (q y), ∏ y : Y, chi (q y) (β y * d y)) =
      ∏ y : Y, ∑ b : ZMod (q y), chi (q y) (b * d y) from
        (Fintype.prod_sum fun (y : Y) (b : ZMod (q y)) => chi (q y) (b * d y)).symm]
  simp only [charSum]
  rw [Fintype.prod_ite_zero, Fintype.card_pi]
  simp [ZMod.card]

omit [∀ u, NeZero (q u)] [Fintype Λ] [DecidableEq Λ] in
theorem agreesOff_iff_forall_sub_eq_zero (X : Set Λ) (s s' : Config fun u => ZMod (q u)) :
    AgreesOff X s s' ↔ ∀ y : (Xᶜ : Set Λ), (s - s') y = 0 := by
  constructor
  · intro h y
    rw [Pi.sub_apply, sub_eq_zero]
    exact h y y.2
  · intro h u hu
    have := h ⟨u, hu⟩
    rwa [Pi.sub_apply, sub_eq_zero] at this

open Classical in
/-- M3, Definition 2.2: the twirl onto `X`, the average of `U M U^*` over the Weyl unitaries
of the complement. -/
def twirl (X : Set Λ) (M : QuditAlgebra fun u => ZMod (q u)) : QuditAlgebra fun u => ZMod (q u) :=
  ((Fintype.card ((y : (Xᶜ : Set Λ)) → ZMod (q y)) : ℂ) ^ 2)⁻¹ •
    ∑ α : (y : (Xᶜ : Set Λ)) → ZMod (q y), ∑ β : (y : (Xᶜ : Set Λ)) → ZMod (q y),
      weyl Xᶜ α β * M * star (weyl Xᶜ α β)

/-- M3, Proposition 3.3: the twirl is the conditional expectation. -/
theorem twirl_eq_condExp (X : Set Λ) (M : QuditAlgebra fun u => ZMod (q u)) :
    twirl X M = condExp X M := by
  classical
  ext s s'
  have hc : (Fintype.card ((y : (Xᶜ : Set Λ)) → ZMod (q y)) : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  simp only [twirl, Matrix.smul_apply, Matrix.sum_apply, weyl_conj_apply, smul_eq_mul,
    phase_shiftBy_mul_star]
  simp only [← Finset.sum_mul, ← Finset.mul_sum]
  simp only [sum_phase]
  rw [condExp_apply]
  by_cases h : AgreesOff X s s'
  · have h' : ∀ y : (Xᶜ : Set Λ), (s - s') y = 0 := (agreesOff_iff_forall_sub_eq_zero X s s').1 h
    simp only [h, h', implies_true, ite_true]
    have hrs : restrict Xᶜ s' = restrict Xᶜ s := by
      funext y
      exact (h y y.2).symm
    rw [Fintype.sum_equiv ((Equiv.neg _).trans (Equiv.addLeft (restrict Xᶜ s)))
      (fun α => M (shiftBy Xᶜ (-α) s) (shiftBy Xᶜ (-α) s'))
      (fun η => M (glue Xᶜ η s) (glue Xᶜ η s')) (fun α => by simp [shiftBy, hrs])]
    rw [sq, mul_inv, mul_assoc, ← mul_assoc _ (Fintype.card _ : ℂ), inv_mul_cancel₀ hc, one_mul]
  · have h' : ¬ ∀ y : (Xᶜ : Set Λ), (s - s') y = 0 := fun h' =>
      h ((agreesOff_iff_forall_sub_eq_zero X s s').2 h')
    simp only [h, h', ite_false]
    simp

open scoped Matrix.Norms.L2Operator

/-- M3, Proposition 3.4 (c): the twirl is a contraction. -/
theorem norm_twirl_le (X : Set Λ) (M : QuditAlgebra fun u => ZMod (q u)) :
    ‖twirl X M‖ ≤ ‖M‖ := by
  classical
  have hc : (Fintype.card ((y : (Xᶜ : Set Λ)) → ZMod (q y)) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have h1 : ∀ α β : (y : (Xᶜ : Set Λ)) → ZMod (q y),
      ‖weyl Xᶜ α β * M * star (weyl Xᶜ α β)‖ = ‖M‖ := fun α β =>
    norm_conj_eq (weyl_mem_unitary Xᶜ α β) M
  have h2 : ‖∑ α : (y : (Xᶜ : Set Λ)) → ZMod (q y), ∑ β : (y : (Xᶜ : Set Λ)) → ZMod (q y),
      weyl Xᶜ α β * M * star (weyl Xᶜ α β)‖ ≤
      (Fintype.card ((y : (Xᶜ : Set Λ)) → ZMod (q y)) : ℝ) ^ 2 * ‖M‖ := by
    refine (norm_sum_le _ _).trans ?_
    refine (Finset.sum_le_sum fun α _ => norm_sum_le _ _).trans ?_
    simp only [h1, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [sq, mul_assoc]
  rw [twirl, norm_smul, norm_inv, norm_pow, RCLike.norm_natCast]
  calc ((Fintype.card ((y : (Xᶜ : Set Λ)) → ZMod (q y)) : ℝ) ^ 2)⁻¹ * ‖_‖
      ≤ ((Fintype.card ((y : (Xᶜ : Set Λ)) → ZMod (q y)) : ℝ) ^ 2)⁻¹ *
          ((Fintype.card ((y : (Xᶜ : Set Λ)) → ZMod (q y)) : ℝ) ^ 2 * ‖M‖) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = ‖M‖ := by rw [← mul_assoc, inv_mul_cancel₀ (pow_ne_zero 2 hc), one_mul]

theorem norm_condExp_le (X : Set Λ) (M : QuditAlgebra fun u => ZMod (q u)) :
    ‖condExp X M‖ ≤ ‖M‖ := by
  rw [← twirl_eq_condExp]
  exact norm_twirl_le X M

/-- M3, Proposition 3.4 (b): the bimodule property, left factor. -/
theorem condExp_mul_left {X : Set Λ} {a : QuditAlgebra fun u => ZMod (q u)}
    (ha : a ∈ localAlgebra X) (M : QuditAlgebra fun u => ZMod (q u)) :
    condExp X (a * M) = a * condExp X M := by
  classical
  rw [← twirl_eq_condExp, ← twirl_eq_condExp, twirl, twirl, mul_smul_comm, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun β _ => ?_
  have hcomm : Commute (weyl Xᶜ α β) a :=
    commute_of_disjoint disjoint_compl_left (isLocal_weyl Xᶜ α β) ha
  rw [← mul_assoc (weyl Xᶜ α β) a M, hcomm.eq, mul_assoc a, mul_assoc a]

/-- M3, Proposition 3.4 (b): the bimodule property, right factor. -/
theorem condExp_mul_right {X : Set Λ} {b : QuditAlgebra fun u => ZMod (q u)}
    (hb : b ∈ localAlgebra X) (M : QuditAlgebra fun u => ZMod (q u)) :
    condExp X (M * b) = condExp X M * b := by
  classical
  rw [← twirl_eq_condExp, ← twirl_eq_condExp, twirl, twirl, smul_mul_assoc, Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun β _ => ?_
  have hcomm : Commute b (star (weyl Xᶜ α β)) :=
    commute_of_disjoint disjoint_compl_right hb (isLocal_weyl Xᶜ α β).star
  rw [mul_assoc (weyl Xᶜ α β * M), ← hcomm.eq, ← mul_assoc, ← mul_assoc, mul_assoc]

/-- M3, Theorem 3.5, the local-approximation estimate: `‖M - E_X M‖ ≤ N_{Xᶜ}(M)`. -/
theorem norm_sub_twirl_le_commNorm (X : Set Λ) (M : QuditAlgebra fun u => ZMod (q u)) :
    ‖M - twirl X M‖ ≤ commNorm (quditNet fun u => ZMod (q u)) Xᶜ M := by
  classical
  have hc : (Fintype.card ((y : (Xᶜ : Set Λ)) → ZMod (q y)) : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hcR : (Fintype.card ((y : (Xᶜ : Set Λ)) → ZMod (q y)) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hM : M = ((Fintype.card ((y : (Xᶜ : Set Λ)) → ZMod (q y)) : ℂ) ^ 2)⁻¹ •
      ∑ _α : (y : (Xᶜ : Set Λ)) → ZMod (q y), ∑ _β : (y : (Xᶜ : Set Λ)) → ZMod (q y), M := by
    simp only [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
    rw [show ((Fintype.card ((y : (Xᶜ : Set Λ)) → ZMod (q y)) : ℂ) ^ 2)⁻¹ *
        ((Fintype.card ((y : (Xᶜ : Set Λ)) → ZMod (q y)) : ℂ) *
          (Fintype.card ((y : (Xᶜ : Set Λ)) → ZMod (q y)) : ℂ)) = 1 by
      rw [sq]; exact inv_mul_cancel₀ (mul_ne_zero hc hc), one_smul]
  have key : M - twirl X M = ((Fintype.card ((y : (Xᶜ : Set Λ)) → ZMod (q y)) : ℂ) ^ 2)⁻¹ •
      ∑ α : (y : (Xᶜ : Set Λ)) → ZMod (q y), ∑ β : (y : (Xᶜ : Set Λ)) → ZMod (q y),
        comm M (weyl Xᶜ α β) * star (weyl Xᶜ α β) := by
    calc M - twirl X M
        = ((Fintype.card ((y : (Xᶜ : Set Λ)) → ZMod (q y)) : ℂ) ^ 2)⁻¹ •
            ∑ _α : (y : (Xᶜ : Set Λ)) → ZMod (q y), ∑ _β : (y : (Xᶜ : Set Λ)) → ZMod (q y), M -
          ((Fintype.card ((y : (Xᶜ : Set Λ)) → ZMod (q y)) : ℂ) ^ 2)⁻¹ •
            ∑ α : (y : (Xᶜ : Set Λ)) → ZMod (q y), ∑ β : (y : (Xᶜ : Set Λ)) → ZMod (q y),
              weyl Xᶜ α β * M * star (weyl Xᶜ α β) := by rw [← hM]; rfl
      _ = _ := by
        simp only [← smul_sub, ← Finset.sum_sub_distrib]
        congr 1
        refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => ?_
        rw [comm_def, sub_mul, mul_assoc M, weyl_mul_star_weyl, mul_one]
  have hN : 0 ≤ commNorm (quditNet fun u => ZMod (q u)) Xᶜ M := commNorm_nonneg _ _ _
  have hterm : ∀ α β : (y : (Xᶜ : Set Λ)) → ZMod (q y),
      ‖comm M (weyl Xᶜ α β) * star (weyl Xᶜ α β)‖ ≤
        commNorm (quditNet fun u => ZMod (q u)) Xᶜ M := fun α β => by
    have hU : ‖weyl Xᶜ α β‖ = 1 := CStarRing.norm_of_mem_unitary (weyl_mem_unitary Xᶜ α β)
    calc ‖comm M (weyl Xᶜ α β) * star (weyl Xᶜ α β)‖
        ≤ ‖comm M (weyl Xᶜ α β)‖ * ‖star (weyl Xᶜ α β)‖ := norm_mul_le _ _
      _ = ‖comm M (weyl Xᶜ α β)‖ := by rw [norm_star, hU, mul_one]
      _ ≤ commNorm (quditNet fun u => ZMod (q u)) Xᶜ M :=
        norm_comm_le_commNorm _ _ (weyl_mem Xᶜ α β) hU.le
  have h2 : ‖∑ α : (y : (Xᶜ : Set Λ)) → ZMod (q y), ∑ β : (y : (Xᶜ : Set Λ)) → ZMod (q y),
      comm M (weyl Xᶜ α β) * star (weyl Xᶜ α β)‖ ≤
      (Fintype.card ((y : (Xᶜ : Set Λ)) → ZMod (q y)) : ℝ) ^ 2 *
        commNorm (quditNet fun u => ZMod (q u)) Xᶜ M := by
    refine (norm_sum_le _ _).trans ?_
    refine (Finset.sum_le_sum fun α _ => norm_sum_le _ _).trans ?_
    refine (Finset.sum_le_sum fun α _ => Finset.sum_le_sum fun β _ => hterm α β).trans ?_
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [sq, mul_assoc]
  rw [key, norm_smul, norm_inv, norm_pow, RCLike.norm_natCast]
  calc ((Fintype.card ((y : (Xᶜ : Set Λ)) → ZMod (q y)) : ℝ) ^ 2)⁻¹ * ‖_‖
      ≤ ((Fintype.card ((y : (Xᶜ : Set Λ)) → ZMod (q y)) : ℝ) ^ 2)⁻¹ *
          ((Fintype.card ((y : (Xᶜ : Set Λ)) → ZMod (q y)) : ℝ) ^ 2 *
            commNorm (quditNet fun u => ZMod (q u)) Xᶜ M) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = _ := by rw [← mul_assoc, inv_mul_cancel₀ (pow_ne_zero 2 hcR), one_mul]

theorem norm_sub_condExp_le_commNorm (X : Set Λ) (M : QuditAlgebra fun u => ZMod (q u)) :
    ‖M - condExp X M‖ ≤ commNorm (quditNet fun u => ZMod (q u)) Xᶜ M := by
  rw [← twirl_eq_condExp]
  exact norm_sub_twirl_le_commNorm X M

/-- M3, Theorem 3.5, the converse: `N_{Xᶜ}(M) ≤ 2 ‖M - E_X M‖`. -/
theorem commNorm_compl_le_two_mul_norm_sub_condExp (X : Set Λ)
    (M : QuditAlgebra fun u => ZMod (q u)) :
    commNorm (quditNet fun u => ZMod (q u)) Xᶜ M ≤ 2 * ‖M - condExp X M‖ :=
  commNorm_le_two_mul_norm_sub quditNet_isCausal disjoint_compl_right (condExp_mem X M)

/-- The qudit net with cyclic alphabets is a net with local approximation (M3, Theorem 3.5). -/
def localApprox : LocalApprox (quditNet fun u => ZMod (q u)) where
  P := condExp
  P_mem := condExp_mem
  norm_sub_P_le := norm_sub_condExp_le_commNorm

@[simp] theorem localApprox_P (X : Set Λ) (M : QuditAlgebra fun u => ZMod (q u)) :
    (localApprox (q := q)).P X M = condExp X M := rfl

end Weyl

end LocalityLean.Qudit

end
