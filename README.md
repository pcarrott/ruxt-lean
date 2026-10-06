# RUXt: Lean Formalisation

A Lean 4 formalisation of [RUXt](https://github.com/pcarrott/soteria/tree/ruxt-dev/ruxt): a refutation algorithm for the type unsoundness of generic Rust libraries, built on under-approximate (UX) reasoning. This project formalises that algorithm and proves it correct for a small Rust-like core language with generic functions, a block-based heap and explicit (de)allocation.

## Building

Building requires [Lean 4](https://lean-lang.org) (installed via
[`elan`](https://github.com/leanprover/elan)); the toolchain version is pinned in
`lean-toolchain`, and [Mathlib](https://github.com/leanprover-community/mathlib4) is fetched
automatically.  From the root of the repository, run

```sh
lake exe cache get   # fetch the Mathlib build cache (first time only)
lake build
```

`lake build` compiles the root module `RUXt.lean`, which imports the whole development.

## What is formalised

* **A small Rust-like core language** with generic functions: syntax, types and type constructors
  with type parameters, a typechecker, and a big-step operational semantics over a block-based
  heap, given in two forms — the full semantics `⇓` (`BigStep`) and an instrumented one `⇓ᵢ`
  (`FrameStep`) — together with the frame properties (`frame_addition`, `frame_subtraction`) and
  the relation between the two (`semantics_preservation`).
* **Assertions and program logics.** A separation-logic assertion language (`Asrt`), symbolic
  assertions, programs and triples parametric on the symbolic values bound by a telescope, and
  triples parametric on *typed subvariants*.  A program logic (`Logic`) is an abstract
  derivability relation on triples, sound (`Logic.Sound`) when every triple it derives holds
  under the under-approximate reading of triples.  A solver (`Solver`) answers satisfiability
  and simplification queries.
* **Summaries and type spaces.** A summary pairs a subvariant (a postcondition describing some
  inhabitants of a type) with a *source*, a generic function template producing them.  A type
  space (`SummCtx`) files summaries by type constructor, starting from the base summaries.
* **The refutation algorithm** (`RUXt/Model/Refute.lean`), parametric on a logic `L` and a
  solver `Θ`:
  * `Library.TryRefute` calls a `safe` library function on summaries picked from the type space
    and either derives a new summary for its output type or, in the error case, produces a
    *witness* program (`Source.witness`) read off a model returned by the solver;
  * `SummCtx.TrySpecialise` extends the type space by specialising a summary, pinning one of its
    type parameters to a type constructor described by other summaries of the space (so that a
    summary inhabiting `List<T>` may be specialised to one inhabiting `List<List<T>>`);
  * `WfSummCtx` combines both rules into well-formed type spaces.

  The definitions in `Model/` are purely syntactic: they never refer to the meaning of
  assertions.

## What is proven

Everything below is fully proven: there is no `sorry`, and the main theorems depend only on Lean's standard axioms (`propext`, `Classical.choice`, `Quot.sound`).

* **Inadequacy** (`inadequacy`, `RUXt/Semantics/Inadequacy.lean`): if a type assignment of a
  library is refuted — the algorithm, run in *some* sound logic with the semantic solver
  `semSolver`, reaches the error case with a witness `e` (`Library.HasRefutedType`) — then the
  library is *inadequate* (`Library.Inadequate`): `e` is a well-typed main program (`SafeMain`)
  whose execution from the empty heap goes wrong.
* Along the way:
  * every well-formed type space is valid (`summCtx_soundness`): each of its summaries is
    reachable, i.e. its source really produces all the states its postcondition describes;
  * the derivation step is sound (`source_reachable`) and so is the specialisation step
    (`Summary.specialise_valid`); the examples `trySpecialise_id_unit` and
    `trySpecialise_id_param` show the specialisation rule firing;
  * the witness program is a well-typed main program (`Summary.witness_safeMain`) and it
    executes into the erroneous state exhibited by the model (`Summary.witness_frameStep`).
* **RISL** (`RUXt/Examples/RISL.lean`): the proof rules of RISL form a sound logic
  (`risl_sound`), so refutations may be carried out in it.
* **Worked refutations** of two unsound libraries, each concluding inadequacy from a concrete
  run of the algorithm:
  * `even_inadequate` (`RUXt/Examples/Even.lean`), a library of even numbers;
  * `box_inadequate` (`RUXt/Examples/Box.lean`), a library of generic boxes whose
    `box → rebox → cycle → drop` sequence exhibits a use-after-free.

## Directory structure

The development is split into a *definitional* half and a *proof* half: `Model/` contains
only the definitions the refutation algorithm is stated in terms of — nothing about the
semantics of assertions — while `Semantics/` contains the proofs leading to the inadequacy
theorem. All paths below are relative to `RUXt/` and all declarations follow the
[Mathlib naming conventions](https://leanprover-community.github.io/contribute/naming.html).

| Path | Contents |
|---|---|
| `Lib/PFun.lean` | Partial maps, with the union/disjointness theory used for heaps. |
| `Lib/Telescopes.lean` | Telescopes: first-class dependent contexts (`Tele`) and their environments (`TeleArg`, nested `Σ`). Objects parameterised by a context are plain functions `TeleArg tt → A`, written with destructuring lambdas `fun ⟨x, y, _⟩ => …`. |
| `Lang/Types/Basic.lean` | Types and type constructors (types with type parameters, referred to by index). |
| `Lang/Types/Params.lean` | Type parameters: tuples of type arguments, concretisation and instantiation, renaming, anonymous forms, matching and the substitutions used by specialisation. |
| `Lang/Expr.lean` | Syntax of the language: values, terms, pure expressions and expressions; evaluation of pure expressions and variable substitution. |
| `Lang/Functions/Basic.lean` | Function implementations and generic function templates. |
| `Lang/Functions/Library.lean` | Function declarations and libraries. |
| `Lang/Typechecker.lean` | The typechecker. |
| `Lang/Semantics.lean` | Heaps and the operational semantics (`⇓` and `⇓ᵢ`), frame properties. |
| `Model/Logic.lean` | Assertions (`Asrt`), symbolic assertions, programs and triples, typed subvariants and the triples parametric on them, logics (`Logic`) and solvers (`Solver`). |
| `Model/Summary/Source.lean` | Sources, and the binding of sources in front of an expression. |
| `Model/Summary/Basic.lean` | Subvariants, summaries, type spaces, base summaries. |
| `Model/Summary/Derive.lean` | Deriving a summary from a call on picked summaries. |
| `Model/Summary/Specialise.lean` | Specialisation of sources, subvariants and summaries. |
| `Model/Witness.lean` | Families of picks for the type parameters of a source and the witness program. |
| `Model/Refute.lean` | The refutation algorithm: `Library.TryRefute`, `SummCtx.TrySpecialise`, `WfSummCtx`. |
| `Semantics/Logic/Asrt.lean` | Semantics of assertions (satisfaction, entailment, equivalence) and well-typed programs (`SafeProgram`). |
| `Semantics/Logic/Basic.lean` | Under-approximate semantics of triples and soundness of a logic. |
| `Semantics/Logic/Poly.lean` | Semantics of triples parametric on typed subvariants. |
| `Semantics/Logic/Solver.lean` | The semantic solver `semSolver` and satisfiability of postconditions. |
| `Semantics/Summary/Subvariant/*.lean` | Semantics of subvariants and of their specialisation. |
| `Semantics/Summary/Source/*.lean` | Semantics of sources, of binding sources and of the specialisation of a source. |
| `Semantics/Summary/Basic.lean` | Validity of summaries and of type spaces; validity of the base summaries. |
| `Semantics/Summary/Derive.lean` | Soundness of the derivation step. |
| `Semantics/Summary/Specialise.lean` | Soundness of the specialisation step. |
| `Semantics/Witness.lean` | Correctness of the witness program. |
| `Semantics/Inadequacy.lean` | What a refutation claims, validity of well-formed type spaces and the inadequacy theorem. |
| `Examples/RISL.lean` | The RISL proof rules and their soundness. |
| `Examples/Calls.lean` | Deriving the postcondition of a call on picked summaries in RISL. |
| `Examples/Even.lean` | The `Even` library and its refutation. |
| `Examples/Box/Library.lean`, `Examples/Box.lean` | The `Box` library and its refutation. |

## Credits and AI disclosure

This project was originally ported from Rocq to Lean using Anthropic Fable 5. Further developments were performed with the help of [Aristotle](https://aristotle.harmonic.fun) by Harmonic.
