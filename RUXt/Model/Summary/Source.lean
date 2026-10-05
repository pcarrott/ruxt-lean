import RUXt.Model.Logic

/-!
# Sources

The sources a summary runs (`Source`): symbolic function templates bundled with their shape.
Also the tools for binding sources in front of an expression: the parameters they contribute
(`boundParams`), the let-binding of the sources themselves, each followed by the chain
rebinding its renamed parameters (`Expr.bindSources`), the renaming keeping those parameters
apart (`PVar.freshen`, `maxNameLen`), and the sharing of a block of typed subvariants among
bound sources (`Source.dropSubvArgs`).
-/

namespace RUXt

/-! ## Sources -/

/-- A source: a symbolic function template bundled with the telescope of the symbolic values
it depends on and its number of type parameters.  The input values of a source are the
parameters of its template. -/
structure Source where
  /-- The telescope of the symbolic values the source depends on. -/
  teleOf : Tele
  /-- The number of type parameters of the source. -/
  arity : ℕ
  /-- The template of the source. -/
  fn : FunTempl teleOf arity

namespace Source

/-- The number of *free* type parameters of a source: those the type constructor it produces
does not use. -/
def freeArity (s : Source) : ℕ := s.fn.ty.freeArity s.arity

/-- The number of input values of a source: one per parameter of its template. -/
abbrev valArity (s : Source) : ℕ := s.fn.valArity

/-- All symbolic values a list of sources depends on. -/
def mergedTeleOf : List Source → Tele :=
  List.foldr (Tele.app ∘ teleOf) [tele]
/-- Total number of input values of a list of sources. -/
def mergedValArity : List Source → ℕ :=
  List.foldr (fun s => Nat.add s.valArity) 0
/-- Total number of free type parameters of a list of sources. -/
def mergedFreeArity : List Source → ℕ :=
  List.foldr (Nat.add ∘ freeArity) 0

/-- The embedding of the type parameters of a source into those of a template binding it: a
type parameter the produced type constructor uses is sent to the one `osel` prescribes for it,
and the free ones to consecutive positions starting at `base`. -/
def ren (s : Source) (osel : List TyIdx) (base : ℕ) : TyIdx → TyIdx :=
  s.fn.ty.mergeRen osel base s.arity

/-- The number of parameters of a source carrying the type parameter `i`. -/
def paramCount (s : Source) (i : TyIdx) : ℕ := s.fn.paramCons.count (.param i)

/-- The number of parameters of a source carrying a type parameter `k` that the selection
`osel` sends to `j`. -/
def selCount (s : Source) (osel : List TyIdx) (j : TyIdx) : ℕ :=
  s.fn.paramCons.countP fun
    | .param k => osel[k]? == some j
    | _ => false

end Source

/-! ## Binding sources -/

/-- The largest length of a name in `xs`. -/
def maxNameLen : List PVar → ℕ :=
  List.foldr (fun x => max x.length) 0
/-- A fresh name for the parameter `x` of the `n`-th bound source: `m + 1` copies of `'x'`
(longer than any name of length at most `m`), then `n` in unary with `'_'`, then `'.'`. -/
def PVar.freshen (m n : ℕ) (x : PVar) : PVar :=
  .ofList (.replicate (m + 1) 'x' ++ .replicate n '_' ++ '.' :: x.toList)

/-- The parameters the sources `srcs` contribute when bound, one per parameter, to parameters
carrying the type constructors `cons`: the parameters of the `n`-th source from the end, renamed
with `PVar.freshen m n`, with their type constructors embedded along `Source.ren`.  The free
type parameters of the sources take consecutive positions starting at `base`. -/
def boundParams (m : ℕ) (cons : List TyConsId) (base : ℕ) : List Source → List (PVar × TyConsId)
  | [] => []
  | s :: srcs =>
    -- Embed the type parameters of `s` at the constructor it is bound to
    let ρ := s.ren (cons.headD .unit).params base
    -- Rename the parameters of `s` apart and embed their type constructors
    s.fn.params.map (fun ⟨x, τ⟩ => (x.freshen m srcs.length, τ.rename ρ))
      -- Continue with the next source, past the free type parameters of `s`
      ++ boundParams m cons.tail (base + s.freeArity) srcs

/-- The expression `body` with the sources `srcs` let-bound in front of it to the parameters
`params`, in order, at the symbolic values `args`.  Each source is bound to the name of its
parameter and read at the type arguments `types` at the type parameters of the type
constructor of that parameter, followed by its own share of the free type arguments `free`. -/
def Expr.bindSources (m : ℕ) {N : ℕ} (types : TyArgs N) (body : Expr)
    (params : List (PVar × TyConsId)) : (srcs : List Source) →
    TyArgs (Source.mergedFreeArity srcs) → TeleArg (Source.mergedTeleOf srcs) → Expr
  | [], _, _ => body
  | s :: srcs, F, args =>
    -- Take the parameter the head source is bound to: its name and type constructor
    let ⟨var, τ⟩ := params.headD ("unreachable", .unit)
    -- Split off the free type arguments of the head source
    let ⟨own, F⟩ := F.splitUniform s.freeArity _
    let e :=
      -- Read the type arguments at the type parameters of `τ`, then the free ones
      let types := types.reindex .unit (τ.params.getD · 0) τ.arity
      let types := types.appendUniform own |>.reindex .unit id s.arity
      -- Instantiate the body of the head source
      let body := s.fn.body |>.apply args.fst |>.apply types
      -- Rebind its parameters to their renamed counterparts
      s.fn.paramNames.foldr (fun x =>
        .letIn (.named x) (.var (PVar.freshen m srcs.length x))) body
    -- Bind the remaining sources in front of `body`
    let body := body.bindSources m types params.tail srcs F args.snd
    -- Bind the head source to its variable
    .letIn (.named var) e body

/-- The typed subvariants `S` with, for each component `j`, the subvariants of the parameters of
`s` carrying a type parameter `osel` sends to `j` removed (`Source.selCount`): the subvariants
left to the sources bound after `s`. -/
def Source.dropSubvArgs (s : Source) {n : ℕ}
    (S : SubvArgs.{0} n) (osel : List TyIdx) : SubvArgs.{0} n :=
  .ofListPad default n ((List.range n).map fun j =>
    ⟨(S.get j).ty, (S.get j).own.drop (s.selCount osel j)⟩)

end RUXt
