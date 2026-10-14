# Conventions

## Mathematics

- **Dynamics.** `A(t) = e^{itH} A e^{-itH}` and the generator `L A = i[H, A]`; statements are
  for `t ≥ 0` unless time reversal is proved.
- **The bounded quantity** is `‖[A(t), B]‖`, with the evolved observable first, stated in the
  form `2‖A‖‖B‖(…)`.
- **Interactions** are finite families indexed by finite supports, so one support may carry
  several terms.
- **Paths** are sequences of supports each crossing the previous one (meeting it and its
  complement), with first contact at the last step; a term never follows itself.
- **Inner products** are linear in the second argument.
- **Distances** are functions `d` with `d(x, x) = 0` and the triangle inequality, not assumed
  symmetric; `d(y, x)` is read from the probe's side.

## Lean

- One definition per concept: nothing is re-created that LocalAlgebrasLean, LinearAQFT or
  BosonicLean defines; a declaration lives in the most general library that can state it.
- `Core` imports only Mathlib, LinearAQFT's net and causal layers and LocalAlgebrasLean; `Qudit`
  adds nothing outside Mathlib and `Core`; `Approx` adds `Qudit`; `Bosonic` adds BosonicLean and
  LinearAQFT. All pins are by commit and move together.
- Namespaces follow the directories under the root `LocalityLean`. Declaration names are ASCII
  and follow Mathlib's naming; lines are at most 100 characters. Each module's header states its
  results with the numbering of the lecture notes.
- No unfinished proofs, no added axioms, no unchecked computation, no blanket import of Mathlib.
  The principal theorems are stated in `verify/Challenge.lean` and proved in
  `verify/Solution.lean`; `lake comparator` checks that the proofs prove exactly these statements
  from the three standard axioms only.

## Notes

- Standard terms, no eponyms except "Lieb–Robinson bound"; terms coined for the notes are listed
  in the front matter.
- A figure wherever a structure is explained.
- Every number in the notes is produced by a named script in `checks/`, named in the chapter's
  end notes.
