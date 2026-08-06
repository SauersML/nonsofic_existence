import Lean
import Audit.DeclFilter

/-!
# Detectors that read the elaborated environment

Adapted from gnomon's `proofs/validation/code/Check.lean` and the budget list
at the head of its `check.py`.  The scans here are the ones that transfer to a
pure proof corpus; gnomon's genetics-specific budgets (conventions, regimes,
equilibria, domain-named arithmetic) do not, and its differential and
metamorphic tiers compare Lean against a shipped Rust implementation, which
this repository does not have.

WHY THIS IS A LEAN METAPROGRAM AND NOT A GREP.  Every question below is about
what a proof TERM is, or about what the kernel actually accepted, and neither
exists in the source text.  gnomon records that three separate text scans of
one such question returned 2, 16 and 3 hits with no overlap in names, and that
one of them reported a word out of a docstring as a theorem.  Lean is
whitespace-insensitive and its proofs are not a regular language; the
environment is the only authority.

## The scans

  AXIOM            transitive axiom closure outside classical Lean's three.
  LAUNDERED_PROP   a named proposition the corpus only ever ASSUMES.  Nothing
                   is ever proved to satisfy it, so every theorem with it as a
                   hypothesis is consistent with it being unsatisfiable, and
                   every theorem refuting it is consistent with it being
                   unsatisfiable too.  This is the general form of the gap the
                   positive control in `SoficPositiveControl.lean` closes.
  UNWITNESSED      a structure with Prop-valued fields that the corpus never
                   exhibits a closed term of: the caller hands over finished
                   mathematics and the corpus never shows it can be finished.
  TAUTOLOGY        the conclusion is syntactically one of the premises.
                   `theorem P_of_P (h : P) : P := h` has a clean axiom report.
  UNCONDITIONAL    a name promising an unconditional result on a type that
                   still carries Prop premises.
  INSTANCE_PREMISE a Prop-valued instance or implicit binder: an assumption
                   written in a syntax that hides it from the signature's
                   reader.
  EMPTY_PREMISE    a premise of an empty type; the theorem is vacuous.
  TRIVIAL          the conclusion is `True`.
  UNUSED           a binder occurring in neither the rest of the type nor the
                   accepted proof term.  KNOWN LOWER BOUND: `omega`, `linarith`
                   and `simp_all` splice every hypothesis in scope into the
                   certificate they emit, so a hypothesis they did not need
                   still occurs in the term and is invisible here.  There is no
                   false-positive direction: occurrence-freedom in a term the
                   kernel accepted proves the binder is deletable.
  DUPLICATE        one proposition proved twice under two names.
  RFL              the proof term is literally `Eq.refl`.
  STALE_DISCLAIMER a docstring describing the result as conditional, on a
                   statement that carries no Prop premise to be conditional
                   ON.  See `mentionsConditionality` for why this scan is
                   here and not in `check.py`.
-/

open Lean Meta Elab Command

namespace Audit

/-- One finding.  `fatal` decides the exit code; everything else is reported
so that the numbers exist before anyone argues about them. -/
structure Finding where
  tag : String
  fatal : Bool
  decl : Name
  detail : String
  deriving Inhabited

/-- Is `n` declared in the corpus under audit, rather than in Mathlib?

`getRoot` and not `isPrefixOf`: they agree on every name in this corpus and
`getRoot` says what is meant. -/
def isOurs (root n : Name) : Bool := n.getRoot == root

/-- Every hand-written declaration of the corpus, taken from the environment
rather than from a list, so a new module cannot escape the audit by not being
mentioned anywhere. -/
def corpusNames (env : Environment) (root : Name) : Array Name :=
  env.constants.fold (init := #[]) fun acc n _ =>
    if isOurs root n && userWritten env n then acc.push n else acc

/-- Strip leading binders, returning the body.

A theorem with binders stores its proof as `fun a b c ↦ Eq.refl _`, so testing
the head of the whole value asks whether a LAMBDA is `Eq.refl`, which is never
true.  gnomon records that the first version of its rfl scan did exactly this
and reported a clean-looking 0 of 0. -/
partial def stripLams : Expr → Expr
  | .lam _ _ b _ => stripLams b
  | .mdata _ b => stripLams b
  | e => e

/-- The value of a declaration.

NOT `ConstantInfo.value?`, which returns `none` for THEOREMS on this toolchain
even though the proof term is present and reachable by matching `.thmInfo`
directly.  Every scan that reads a proof term went silent when it trusted
`value?` -- including the axiom traversal, which stopped descending through
proofs entirely and would therefore have reported a clean closure for a corpus
with a `sorry` in it.  `scripts/Calibrate.lean` is what caught this, and it now
asserts the descent explicitly. -/
def valueOf? : ConstantInfo → Option Expr
  | .thmInfo v => some v.value
  | .defnInfo v => some v.value
  | .opaqueInfo v => some v.value
  | _ => none

/-! ## AXIOM -/

/-- Axiom-closure traversal state. -/
structure AxiomState where
  visited : NameSet := {}
  axioms : Array Name := #[]

/-- Walk the transitive closure of `c` through the environment, accumulating
axioms.

Written out rather than calling `Lean.CollectAxioms.collect`, which this
toolchain's module system does not export to downstream code -- the public
`Lean.collectAxioms` wrapper is exported, but it allocates a fresh visited set
per call, and the whole point here is to sweep thousands of roots against ONE
shared set.  Per-root closures over a corpus this size are quadratic and do not
finish. -/
partial def collectFrom (env : Environment) (c : Name) : StateM AxiomState Unit := do
  unless (← get).visited.contains c do
    modify fun s => { s with visited := s.visited.insert c }
    match env.find? c with
    | some (.axiomInfo v) =>
        modify fun s => { s with axioms := s.axioms.push c }
        v.type.getUsedConstants.forM (collectFrom env)
    | some ci =>
        ci.type.getUsedConstants.forM (collectFrom env)
        if let some val := valueOf? ci then
          val.getUsedConstants.forM (collectFrom env)
        if let .inductInfo v := ci then
          v.ctors.forM (collectFrom env)
    | none => pure ()

/-- Axioms reachable from `roots`, sharing one visited set so the sweep over
the whole corpus stays a single traversal. -/
def axiomClosure (env : Environment) (roots : Array Name) : Array Name :=
  (((roots.forM (collectFrom env)).run {}).2).axioms

/-- Corpus declarations that reach `target`, capped: the point is to name a
place to start reading, not to enumerate every debtor. -/
def debtorsOf (env : Environment) (names : Array Name) (target : Name)
    (cap : Nat := 5) : Array Name := Id.run do
  let mut out := #[]
  for n in names do
    if out.size ≥ cap then break
    if (axiomClosure env #[n]).contains target then out := out.push n
  return out

def axiomScan (env : Environment) (names : Array Name) (allowed : List Name) :
    Array Finding := Id.run do
  let bad := (axiomClosure env names).filter fun a => !allowed.contains a
  let mut out := #[]
  for a in bad do
    out := out.push
      { tag := "AXIOM", fatal := true, decl := a,
        detail := s!"reached from {(debtorsOf env names a).toList}" }
  return out

/-! ## Established heads: the shared core of LAUNDERED_PROP and UNWITNESSED

A corpus declaration ESTABLISHES a head constant `H` when its type, after the
telescope, concludes in `H …` (or in `Nonempty (H …)`) and its telescope holds
no `Prop` argument.  The Prop-argument condition is the whole point: a witness
that itself needs a hypothesis discharged has not established anything, it has
relocated the obligation into a premise. -/

/-- Head constant of a type, if it has one. -/
def headConst? (e : Expr) : Option Name := e.getAppFn.constName?

/-- Prop-valued classes that are smuggled ASSUMPTIONS rather than ordinary
mathematical structure.

The distinction matters and getting it wrong cost this scan its first real
verdict.  `Finite` is `class Finite (α : Sort*) : Prop`, so a positive control
stated as `theorem isLEF_of_finite (G) [Group G] [Finite G] : IsLEF G` has a
Prop argument in its telescope -- and a rule that says "any Prop argument means
this is conditional" therefore reports `IsLEF` as never established, which is
precisely backwards: that theorem is the thing that establishes it.  A theorem
about a finite group is not assuming finite groups exist, it is naming the
category it is stated in.

A theorem carrying `[Fact (p < 1)]`, by contrast, IS assuming `p < 1`.  So an
instance binder counts as an obligation only when its class is one of these.
Written as unresolved name literals because this module must not import the
corpus or Mathlib. -/
def assumptionClasses : List Name := [`Fact, `Nonempty, `Inhabited]

/-- Prose describing a result as not yet established.

WHY THIS SCAN MOVED OUT OF `check.py`.  The source-text version asked only
whether a comment contains one of these words, and on this corpus that is a
question with four answers and no way to grade them: `glTwo_eq_elementary`
says "conditional on the rose-graph `K₁` input" and takes
`(hscalar : ScalarReduction _)` as a hypothesis, so the prose is exactly
right.  A text scan cannot see that hypothesis, so its only green state was
one where a true sentence had been deleted -- a gate that pays for silence
with documentation is worse than no gate.

The environment can see both halves, so the question becomes decidable and
sharper than the original: prose claiming conditionality on a statement with
NO Prop premise to be conditional on.  That is the disclaimer that is
genuinely stale, and it is the one worth failing a run over.

COVERAGE DROPPED IN THE MOVE, stated rather than left to be discovered:
module docstrings (`/-! ... -/`) belong to no declaration and are invisible
here, and so is prose on a `def`.  `BinaryLeavittDiagonal.lean`'s module
docstring was one of the four original hits, and is no longer checked by
anything. -/
def disclaimerPhrases : List String :=
  ["conditional", "candidate", "proposed", "not proved", "unproved",
   "not yet proved", "assumed rather than", "remains an assumption"]

/-- Case-insensitive substring test against `disclaimerPhrases`.  `splitOn`
rather than a regex because Lean has no regex and this needs none. -/
def mentionsConditionality (s : String) : Bool :=
  let lower := s.toLower
  disclaimerPhrases.any fun p =>
    let hits := (lower.splitOn p).length - 1
    -- "unconditional(ly)" contains "conditional"; a substring hit inside a
    -- word that asserts the opposite is not a disclaimer.
    let shielded := (lower.splitOn ("un" ++ p)).length - 1
    hits > shielded

/-- Does this binder relocate a mathematical obligation onto the caller?

Prop-valued, and NOT an instance binder of an ordinary structural class. -/
def isObligation (t : Expr) (bi : BinderInfo) (isP : Bool) : Bool :=
  isP && (bi != .instImplicit ||
    (headConst? t |>.map assumptionClasses.contains |>.getD true))

/-- Every head constant the corpus proves or constructs UNCONDITIONALLY, in one
pass.

One pass, and not a search per question: the environment holds all of Mathlib,
so asking "is there a witness for `S`" by walking `env.constants` once per `S`
is (structures asked about) x (constants in Mathlib) telescopes.  gnomon
records that exact shape not finishing inside fifteen minutes. -/
def establishedHeads (env : Environment) (names : Array Name) : MetaM NameSet := do
  let mut out : NameSet := {}
  for n in names do
    let some ci := env.find? n | continue
    unless (match ci with
            | .defnInfo _ | .ctorInfo _ | .thmInfo _ => true
            | _ => false) do continue
    let (h?, unconditional) ← forallTelescope ci.type fun args body ↦ do
      for a in args do
        let t ← inferType a
        let bi := (← a.fvarId!.getDecl).binderInfo
        if isObligation t bi (← isProp t) then return (none, false)
      -- Either a term of `H …`, or a proof of `Nonempty (H …)`: a theorem
      -- witnesses a Prop-valued head, a `Nonempty` proof a data one.
      let body := match body.getAppFn.constName? with
        | some ``Nonempty => (body.getAppArgs[0]?).getD body
        | _ => body
      return (headConst? body, true)
    if let some h := h? then out := out.insert h
    -- A structure is also witnessed when its CONSTRUCTOR appears inside the
    -- proof term of an unconditional declaration, even though the conclusion
    -- is about something else.  `isSofic_of_fintype` builds a `SoficModel`
    -- and concludes `IsSofic G`; reading conclusions alone reported
    -- `SoficModel` as never constructed while the construction sat in the
    -- proof.
    if unconditional then
      if let some val := valueOf? ci then
        for c in val.getUsedConstants do
          match c with
          | .str parent "mk" => out := out.insert parent
          | _ => pure ()
  return out

/-- Corpus constants that are proposition-formers: `∀ …, Prop`. -/
def propFormers (env : Environment) (names : Array Name) : MetaM (Array Name) := do
  let mut out := #[]
  for n in names do
    let some ci := env.find? n | continue
    unless (match ci with
            | .defnInfo _ | .inductInfo _ => true
            | _ => false) do continue
    let isFormer ← forallTelescope ci.type fun _ body ↦
      pure (match body with
            | .sort l => l == Level.zero
            | _ => false)
    if isFormer then out := out.push n
  return out

/-- Structure fields whose type is a `Prop`.  Such a parameter is a
CERTIFICATE: the caller hands over finished mathematics. -/
def propFields (env : Environment) (S : Name) : MetaM (Array Name) := do
  let some info := getStructureInfo? env S | return #[]
  let mut out := #[]
  for f in info.fieldNames do
    let some proj := env.find? (S ++ f) | continue
    -- The `isProp` test MUST run INSIDE the telescope.  Returning the body out
    -- of `forallTelescopeReducing` leaks the fvars it bound, and the check then
    -- runs where they do not exist -- surfacing much later as `unknown free
    -- variable`, nowhere near the cause.
    let isP ← forallTelescope proj.type fun _ b ↦ isProp b
    if isP then out := out.push f
  return out

/-- LAUNDERED_PROP and UNWITNESSED, which share the one pass above. -/
def vacuityScan (env : Environment) (names : Array Name) : MetaM (Array Finding) := do
  let established ← establishedHeads env names
  let mut out := #[]
  for p in ← propFormers env names do
    unless established.contains p do
      out := out.push
        { tag := "LAUNDERED_PROP", fatal := false, decl := p,
          detail := "named proposition the corpus only ever assumes: nothing is \
ever proved to satisfy it, so a theorem refuting it is equally consistent with \
it being unsatisfiable" }
  for n in names do
    let fields ← propFields env n
    if !fields.isEmpty && !established.contains n then
      out := out.push
        { tag := "UNWITNESSED", fatal := false, decl := n,
          detail := s!"structure with Prop-valued fields {fields.toList} that the \
corpus never exhibits a closed term of" }
  return out

/-! ## Per-declaration shape scans -/

/-- Words that promise the HEADLINE result, not merely an existence statement.

`exists` and `_not_` were here and produced 1195 findings on a 5269-declaration
corpus, which is not a gate, it is a mailing list.  Lean's naming convention is
`exists_foo_of_bar` for conditional lemmas, so "exists" in a name carries no
claim at all; `_not_` fares the same.  What the root docstring actually
promises is that no CONDITIONAL result is advertised as THE existence theorem,
so these are the words that only a headline claim would use. -/
def claimWords : List String :=
  ["unconditional", "nonsofic", "theorema", "theoremb"]

/-- Declared directly in the corpus root namespace, i.e. `Corpus.foo` and not
`Corpus.Sub.foo`.  Headline results live at the root; the deep namespaces are
machinery, where a claim word is describing the subject matter rather than
making a claim. -/
def isHeadlineName : Name → Bool
  | .str (.str .anonymous _) _ => true
  | _ => false

/-- Does this name promise the headline result?

Matched against the LAST COMPONENT, never the full name.  Matching
`n.toString` tests the NAMESPACE too, and this corpus is called
`NonsoficGroupsExist` -- so the claim word "nonsofic" matched every single
declaration at the root and the scan reported 99 of them, `mul_mem_tableDomain`
first.  A corpus named after its own headline claim makes that mistake
invisible in the count and obvious in the first example. -/
def promisesClaim (n : Name) : Bool :=
  isHeadlineName n &&
    (match n with
     | .str _ f => claimWords.any fun w ↦ (f.toLower.splitOn w).length > 1
     | _ => false)

/-- Empty types: a premise of one makes the theorem vacuous. -/
def emptyTypes : List Name := [``False, ``Empty, ``PEmpty]

/-- Positions of `forallE` binders whose variable does not occur in the rest of
the TYPE.  Index 0 is outermost. -/
partial def typeUnused : Expr → Nat → Array (Nat × Name) → Array (Nat × Name)
  | .forallE nm _ b _, i, acc =>
      typeUnused b (i + 1) (if b.hasLooseBVar 0 then acc else acc.push (i, nm))
  | _, _, acc => acc

/-- Positions of `lam` binders unused in the proof TERM, and how many binders
the term abstracts.

The count matters.  A term may be eta-short of its type's telescope, and a
binder the term never abstracts is passed on to whatever the term reduces to
rather than discarded, so positions at or beyond the count are not reported.
That is the conservative direction. -/
partial def valUnused : Expr → Nat → Array Nat → (Array Nat × Nat)
  | .lam _ _ b _, i, acc =>
      valUnused b (i + 1) (if b.hasLooseBVar 0 then acc else acc.push i)
  | _, i, acc => (acc, i)

/-- Deliberate, by Lean's own convention for an intentionally unused binder --
the leading underscore its `unusedVariables` linter respects.  That keeps the
scan silent with no allow-list, and makes the underscore an admission a
reader can grep for rather than a way around the check. -/
def deliberate (n : Name) : Bool := n.toString.startsWith "_"

def declScan (env : Environment) (names : Array Name) : MetaM (Array Finding) := do
  let mut out := #[]
  let mut byType : Std.HashMap String Name := {}
  for n in names do
    let some ci := env.find? n | continue
    unless (match ci with | .thmInfo _ => true | _ => false) do continue

    -- TAUTOLOGY / UNCONDITIONAL / INSTANCE_PREMISE / EMPTY_PREMISE / TRIVIAL
    let shape ← forallTelescope ci.type fun args body ↦ do
      let mut taut := false
      let mut propPremise := false
      let mut hidden : Array Name := #[]
      let mut empty : Array Name := #[]
      for a in args do
        let t ← inferType a
        unless ← isProp t do continue
        propPremise := true
        if t == body then taut := true
        if let some h := headConst? t then
          if emptyTypes.contains h then empty := empty.push h
        -- Only instance-syntax ASSUMPTIONS.  Flagging every implicit Prop
        -- binder reported 256 declarations, nearly all of them ordinary
        -- side conditions written `{h : a ≠ b}` so they can be inferred from
        -- later arguments -- normal Lean, not smuggled content.
        let fv := a.fvarId!
        let bi := (← fv.getDecl).binderInfo
        if bi == .instImplicit &&
            (headConst? t |>.map assumptionClasses.contains |>.getD false) then
          hidden := hidden.push (← fv.getUserName)
      return (taut, propPremise, hidden, empty, body.isConstOf ``True)
    let (taut, propPremise, hidden, empty, trivialConcl) := shape

    if taut then
      out := out.push
        { tag := "TAUTOLOGY", fatal := true, decl := n,
          detail := "the conclusion is syntactically one of the premises" }
    let promisesUnconditional := promisesClaim n
    if propPremise && promisesUnconditional then
      out := out.push
        { tag := "UNCONDITIONAL", fatal := true, decl := n,
          detail := "the name promises an unconditional result; the type carries \
Prop premises" }
    unless hidden.isEmpty do
      out := out.push
        { tag := "ASSUMPTION_INSTANCE", fatal := false, decl := n,
          detail := s!"assumptions in instance syntax: {hidden.toList}" }
    unless empty.isEmpty do
      out := out.push
        { tag := "EMPTY_PREMISE", fatal := true, decl := n,
          detail := s!"premise of an empty type {empty.toList}: vacuously true" }
    if trivialConcl then
      out := out.push
        { tag := "TRIVIAL", fatal := false, decl := n, detail := "concludes `True`" }

    -- STALE_DISCLAIMER.  `propPremise` is the whole test: a docstring may call
    -- a result conditional exactly when the type says what it is conditional
    -- on.  Without that guard this is the text scan again, and it fires on
    -- four accurate sentences.
    if let some doc ← findDocString? env n then
      if mentionsConditionality doc && !propPremise then
        out := out.push
          { tag := "STALE_DISCLAIMER", fatal := true, decl := n,
            detail := "the docstring describes the result as conditional or \
unproved; the statement carries no Prop premise to be conditional on" }

    -- UNUSED
    let some val := valueOf? ci | continue
    let deadType := typeUnused ci.type 0 #[]
    let (deadVal, lams) := valUnused val 0 #[]
    let dead := deadType.filter fun (i, nm) ↦
      i < lams && deadVal.contains i && !deliberate nm
    unless dead.isEmpty do
      out := out.push
        { tag := "UNUSED", fatal := false, decl := n,
          detail := s!"binders occurring in neither the rest of the type nor the \
proof term: {(dead.map Prod.snd).toList}" }

    -- DUPLICATE
    let key := toString ci.type
    if let some other := byType[key]? then
      out := out.push
        { tag := "DUPLICATE", fatal := false, decl := n,
          detail := s!"same proposition already proved as {other}" }
    else
      byType := byType.insert key n

    -- RFL
    -- Both spellings.  `rfl` is its own constant (`theorem rfl := Eq.refl a`),
    -- and which one survives elaboration depends on how the proof was written;
    -- testing only `Eq.refl` reports a clean-looking 0 of 0 on a corpus full of
    -- `:= rfl`.
    let head := (stripLams val).getAppFn
    if head.isConstOf ``Eq.refl || head.isConstOf ``rfl then
      -- A `@[simp]` lemma proved by `rfl` is a deliberate API lemma -- it makes
      -- a definitional fact available to `simp`, which is the whole reason to
      -- state it.  96 of the corpus's hits were exactly that (`_apply`,
      -- `_val`, `_coe`).  The interesting case is an ordinary theorem, stated
      -- as though it had content, that holds by definition.
      unless (← getSimpTheorems).isLemma (.decl n) do
        out := out.push
          { tag := "RFL", fatal := false, decl := n,
            detail := "non-simp theorem whose proof term is `Eq.refl`" }
  return out

/-! ## Driver -/

def allScans (env : Environment) (root : Name) (allowed : List Name) :
    MetaM (Array Finding) := do
  let names := corpusNames env root
  let mut out := axiomScan env names allowed
  out := out ++ (← vacuityScan env names)
  out := out ++ (← declScan env names)
  return out

end Audit
