/-
Copyright (c) 2026 LocalityLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LocalityLean contributors
-/
import LocalityLean.Qudit.Config
import LocalAlgebrasLean.Qudit.Relabel

/-!
# Relabelling covariance (now in LocalAlgebrasLean)

M2, Proposition 4.4, moved to LocalAlgebrasLean; the names are exported here under
`LocalityLean.Qudit`.
-/

namespace LocalityLean.Qudit

export LocalAlgebrasLean.Qudit (
  configCongr configCongr_symm_apply agreesOff_image_iff restrict_image_eq_iff relabel
  relabel_apply IsLocal.relabel relabel_symm_relabel relabel_relabel_symm isLocal_relabel_iff
  relabel_localAlgebra)

end LocalityLean.Qudit
