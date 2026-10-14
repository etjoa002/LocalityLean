/-
Copyright (c) 2026 LocalityLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LocalityLean contributors
-/
import LocalityLean.Qudit.Config

/-!
# Single-site operators

For a uniform alphabet `α` on the sites, the operator `siteOp u m` acts by the matrix `m` at the
site `u` and trivially elsewhere. It is local to `{u}`; operators at the same site multiply as
their matrices, operators at distinct sites commute, and the product of operators at distinct
sites has the entries `m (s u) (s'' u) * m' (s v) (s'' v)`. These are the primitives for the
witnesses of M2 (Section 6) and for any formalization of qudit lattices that needs local
operators at a site.

## Main definitions

* `LocalityLean.Qudit.siteOp`.

## Main statements

* `LocalityLean.Qudit.isLocal_siteOp`, `siteOp_mul_same`, `siteOp_commute_of_ne`,
  `siteOp_mul_apply_of_ne`, `star_siteOp`.
-/

noncomputable section

namespace LocalityLean.Qudit

variable {Λ : Type*} {α : Type*}

open Classical in
/-- The operator acting by `m` at the site `u` and trivially elsewhere. -/
def siteOp (u : Λ) (m : Matrix α α ℂ) : QuditAlgebra (fun _ : Λ => α) :=
  Matrix.of fun s s' => if AgreesOff {u} s s' then m (s u) (s' u) else 0

open Classical in
theorem siteOp_apply (u : Λ) (m : Matrix α α ℂ) (s s' : Config (fun _ : Λ => α)) :
    siteOp u m s s' = if AgreesOff {u} s s' then m (s u) (s' u) else 0 := rfl

theorem isLocal_siteOp (u : Λ) (m : Matrix α α ℂ) : IsLocal {u} (siteOp u m) := by
  constructor
  · intro s s' h; simp [siteOp_apply, h]
  · intro s s' r r' hs hr h1 h2
    have e1 : s u = r u := congrFun h1 ⟨u, rfl⟩
    have e2 : s' u = r' u := congrFun h2 ⟨u, rfl⟩
    simp [siteOp_apply, hs, hr, e1, e2]

theorem siteOp_sub (u : Λ) (m m' : Matrix α α ℂ) :
    siteOp u (m - m') = siteOp u m - siteOp u m' := by
  ext s s'
  simp only [siteOp_apply, Matrix.sub_apply]
  split_ifs <;> simp

theorem star_siteOp (u : Λ) (m : Matrix α α ℂ) : star (siteOp u m) = siteOp u (star m) := by
  ext s s'
  rw [Matrix.star_apply, siteOp_apply, siteOp_apply]
  by_cases h : AgreesOff {u} s s'
  · simp [h, h.symm, Matrix.star_apply]
  · have h' : ¬ AgreesOff {u} s' s := fun h' => h h'.symm
    simp [h, h']

variable [Fintype Λ] [DecidableEq Λ] [Fintype α]

/-- Operators at the same site multiply as their matrices. -/
theorem siteOp_mul_same (u : Λ) (m m' : Matrix α α ℂ) :
    siteOp u m * siteOp u m' = siteOp u (m * m') := by
  classical
  ext s s''
  rw [Matrix.mul_apply, siteOp_apply]
  by_cases h : AgreesOff {u} s s''
  · rw [ite_eq_left h, Matrix.mul_apply]
    have hf : ∀ s' ∈ (Finset.univ : Finset (Config (fun _ : Λ => α))),
        s' ∉ Finset.univ.image (Function.update s u) →
          siteOp u m s s' * siteOp u m' s' s'' = 0 := by
      intro s' _ hs'
      have : ¬ AgreesOff {u} s s' := by
        intro hs
        apply hs'
        refine Finset.mem_image.mpr ⟨s' u, Finset.mem_univ _, ?_⟩
        funext v
        by_cases hv : v = u
        · subst hv; simp
        · rw [Function.update_of_ne hv]
          exact hs v (by simpa using hv)
      simp [siteOp_apply, this]
    rw [← Finset.sum_subset (Finset.subset_univ _) hf,
      Finset.sum_image (fun k _ k' _ hk => Function.update_injective s u hk)]
    refine Finset.sum_congr rfl fun k _ => ?_
    have h1 : AgreesOff {u} s (Function.update s u k) := fun v hv =>
      (Function.update_of_ne (by simpa using hv) k s).symm
    have h2 : AgreesOff {u} (Function.update s u k) s'' := h1.symm.trans h
    rw [siteOp_apply, siteOp_apply, ite_eq_left h1, ite_eq_left h2, Function.update_self]
  · rw [ite_eq_right h]
    refine Finset.sum_eq_zero fun s' _ => ?_
    by_cases h1 : AgreesOff {u} s s'
    · have h2 : ¬ AgreesOff {u} s' s'' := fun h2 => h (h1.trans h2)
      simp [siteOp_apply, h2]
    · simp [siteOp_apply, h1]

/-- Operators at distinct sites commute (causality). -/
theorem siteOp_commute_of_ne {u v : Λ} (huv : u ≠ v) (m m' : Matrix α α ℂ) :
    Commute (siteOp u m) (siteOp v m') :=
  commute_of_disjoint (Set.disjoint_singleton.mpr huv) (isLocal_siteOp u m) (isLocal_siteOp v m')

/-- The entries of a product of operators at distinct sites. -/
theorem siteOp_mul_apply_of_ne {u v : Λ} (huv : u ≠ v) (m m' : Matrix α α ℂ)
    (s s'' : Config (fun _ : Λ => α)) (h : AgreesOff ({u} ∪ {v}) s s'') :
    (siteOp u m * siteOp v m') s s'' = m (s u) (s'' u) * m' (s v) (s'' v) := by
  rw [mul_apply_eq_mix (Set.disjoint_singleton.mpr huv) (isLocal_siteOp u m)
    (isLocal_siteOp v m') s s'']
  have h1 : AgreesOff {u} s (mix {u} s s'') := mix_agreesOff_left {u} s s''
  have h2 : AgreesOff {v} (mix {u} s s'') s'' := (mix_agreesOff_right {u} {v} s s'').2 h
  have e1 : mix {u} s s'' u = s'' u := by simp [mix]
  have e2 : mix {u} s s'' v = s v := by simp [mix, huv.symm]
  rw [siteOp_apply, siteOp_apply, ite_eq_left h1, ite_eq_left h2, e1, e2]

end LocalityLean.Qudit

end
