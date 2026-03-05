import Lean

namespace DeepCopy

structure State where
  str : Std.HashMap USize String := {}
  nat : Std.HashMap USize Nat := {}
  int : Std.HashMap USize Int := {}
  name : Std.HashMap USize Lean.Name := {}
  imports : Std.HashMap USize Lean.Import := {}
  fvar : Std.HashMap USize Lean.FVarId := {}
  mvar : Std.HashMap USize Lean.MVarId := {}
  lmvar : Std.HashMap USize Lean.LMVarId := {}
  level : Std.HashMap USize Lean.Level := {}
  lit : Std.HashMap USize Lean.Literal := {}
  posRaw : Std.HashMap USize String.Pos.Raw := {}
  strRaw : Std.HashMap USize Substring.Raw := {}
  sourceInfo : Std.HashMap USize Lean.SourceInfo := {}
  preresolved : Std.HashMap USize Lean.Syntax.Preresolved := {}
  syntaxes : Std.HashMap USize Lean.Syntax := {}
  dataValue : Std.HashMap USize Lean.DataValue := {}
  mdata : Std.HashMap USize Lean.MData := {}
  expr : Std.HashMap USize Lean.Expr := {}

abbrev M := StateM State

unsafe
def withCache {α : Type}
    (getHM : State → Std.HashMap USize α)
    (insert : USize → α → State → State)
    (objKey : α) (mk : M α) : M α := do
  let key := ptrAddrUnsafe objKey
  match (getHM (← get)).get? key with
  | some x => return x
  | none =>
    let res ← mk
    modify (insert key res)
    return res

unsafe def withCacheStr := withCache State.str
  (fun key val state ↦ {state with str := state.str.insert key val})
unsafe def withCacheNat := withCache State.nat
  (fun key val state ↦ {state with nat := state.nat.insert key val})
unsafe def withCacheInt := withCache State.int
  (fun key val state ↦ {state with int := state.int.insert key val})
unsafe def withCacheName := withCache State.name
  (fun key val state ↦ {state with name := state.name.insert key val})
unsafe def withCacheImport := withCache State.imports
  (fun key val state ↦ {state with imports := state.imports.insert key val})
unsafe def withCacheFvar := withCache State.fvar
  (fun key val state ↦ {state with fvar := state.fvar.insert key val})
unsafe def withCacheMvar := withCache State.mvar
  (fun key val state ↦ {state with mvar := state.mvar.insert key val})
unsafe def withCacheLMvar := withCache State.lmvar
  (fun key val state ↦ {state with lmvar := state.lmvar.insert key val})
unsafe def withCacheLevel := withCache State.level
  (fun key val state ↦ {state with level := state.level.insert key val})
unsafe def withCacheLit := withCache State.lit
  (fun key val state ↦ {state with lit := state.lit.insert key val})
unsafe def withCacheSourceInfo := withCache State.sourceInfo
  (fun key val state ↦
  {state with sourceInfo := state.sourceInfo.insert key val})
unsafe def withCachePreresolved := withCache State.preresolved
  (fun key val state ↦
  {state with preresolved := state.preresolved.insert key val})
unsafe def withCacheSyntax := withCache State.syntaxes
  (fun key val state ↦
  {state with syntaxes := state.syntaxes.insert key val})
unsafe def withCacheDataValue := withCache State.dataValue
  (fun key val state ↦
  {state with dataValue := state.dataValue.insert key val})
unsafe def withCacheMdata := withCache State.mdata
  (fun key val state ↦ {state with mdata := state.mdata.insert key val})
unsafe def withCacheExpr := withCache State.expr
  (fun key val state ↦ {state with expr := state.expr.insert key val})


end DeepCopy

open DeepCopy

def Bool.deepCopy : Bool → Bool
| true => true
| false => false

unsafe
def String.deepCopy (s : String) : M String :=
  withCacheStr s <| return ofList s.toList

unsafe
def Nat.deepCopy (n : Nat) : M Nat :=
  withCacheNat n <| match n.repr.toNat? with
  | none => return 0
  | some x => return x

unsafe
def Int.deepCopy (n : Int) : M Int :=
  withCacheInt n <| match n with
  | .ofNat n => .ofNat <$> n.deepCopy
  | .negSucc n => .negSucc <$> n.deepCopy

unsafe
def Lean.Name.deepCopy (name : Name) : M Name :=
  withCacheName name <| match name with
  | anonymous => return anonymous
  | str name s => return str (← name.deepCopy) (← s.deepCopy)
  | num name n => return num (← name.deepCopy) (← n.deepCopy)

unsafe
def Lean.Import.deepCopy (i : Import) : M Import :=
  withCacheImport i <| return {
    «module» := ← i.«module».deepCopy
    importAll := i.importAll.deepCopy
    isExported : Bool := i.isExported.deepCopy
    isMeta     : Bool := i.isMeta.deepCopy }

unsafe
def Lean.FVarId.deepCopy (fvar : FVarId) : M FVarId :=
  withCacheFvar fvar <| return {
    name := ← fvar.name.deepCopy }
unsafe
def Lean.MVarId.deepCopy (mvar : MVarId) : M MVarId :=
  withCacheMvar mvar <| return {
    name := ← mvar.name.deepCopy }
unsafe
def Lean.LMVarId.deepCopy (lmvar : LMVarId) : M LMVarId :=
  withCacheLMvar lmvar <| return {
    name := ← lmvar.name.deepCopy }
def Lean.BinderInfo.deepCopy : BinderInfo → BinderInfo
| default => default
| implicit => implicit
| strictImplicit => strictImplicit
| instImplicit => instImplicit
unsafe
def Lean.Level.deepCopy (l : Level) : M Level :=
  withCacheLevel l <| match l with
  | zero => return zero
  | succ l => return succ (← l.deepCopy)
  | max a b => return max (← a.deepCopy) (← b.deepCopy)
  | imax a b => return imax (← a.deepCopy) (← b.deepCopy)
  | param l => return param (← l.deepCopy)
  | mvar v => return mvar (← v.deepCopy)
unsafe
def Lean.Literal.deepCopy (l : Literal) : M Literal :=
  withCacheLit l <| match l with
  | natVal val => natVal <$> val.deepCopy
  | strVal val => strVal <$> val.deepCopy

unsafe
def String.Pos.Raw.deepCopy (pos : Raw) : M Raw := return {
  byteIdx := ← pos.byteIdx.deepCopy }
unsafe
def Substring.Raw.deepCopy (s : Raw) : M Raw := return {
  str := ← s.str.deepCopy
  startPos := ← s.startPos.deepCopy
  stopPos := ← s.startPos.deepCopy }
unsafe
def Lean.SourceInfo.deepCopy (si : SourceInfo) : M SourceInfo :=
  withCacheSourceInfo si <| match si with
  | .original leading pos trailing endPos =>
    return .original (← leading.deepCopy)
      (← pos.deepCopy) (← trailing.deepCopy) (← endPos.deepCopy)
  | .synthetic pos endPos canonical =>
    return .synthetic (← pos.deepCopy)
      (← endPos.deepCopy) canonical.deepCopy
  | .none => return .none
unsafe
def Lean.Syntax.Preresolved.deepCopy (p : Preresolved) : M Preresolved :=
  withCachePreresolved p <| match p with
  | «namespace» ns => return «namespace» (← ns.deepCopy)
  | decl n fields => return decl (← n.deepCopy) (← fields.mapM String.deepCopy)
unsafe
def Lean.Syntax.deepCopy (stx : Syntax) : M Syntax :=
  withCacheSyntax stx <| match stx with
  | missing => return missing
  | node info kind args =>
    return node (← info.deepCopy)
      (← kind.deepCopy) (← args.mapM deepCopy)
  | atom info val => return atom (← info.deepCopy) (← val.deepCopy)
  | ident info rawVal val preresolved =>
    return ident (← info.deepCopy) (← rawVal.deepCopy)
      (← val.deepCopy) (← preresolved.mapM Preresolved.deepCopy)
unsafe
def Lean.DataValue.deepCopy (dv : DataValue) : M DataValue :=
  withCacheDataValue dv <| match dv with
  | ofString v => return ofString (← v.deepCopy)
  | ofBool v => return ofBool v.deepCopy
  | ofName v => return ofName (← v.deepCopy)
  | ofNat v => return ofNat (← v.deepCopy)
  | ofInt v => return ofInt (← v.deepCopy)
  | ofSyntax v => return ofSyntax (← v.deepCopy)
unsafe
def Lean.MData.deepCopy (m : MData) : M MData :=
  withCacheMdata m <| return {
  entries := ← m.entries.mapM (fun (name, value) ↦
    return (← name.deepCopy, ← value.deepCopy) ) }

unsafe
def Lean.Expr.deepCopy (e : Expr) : M Expr :=
  withCacheExpr e <| match e with
  | bvar deBruijnIndex => return bvar (← deBruijnIndex.deepCopy)
  | fvar fvarId => return fvar (← fvarId.deepCopy)
  | mvar mvarId => return mvar (← mvarId.deepCopy)
  | sort u => return sort (← u.deepCopy)
  | const declName us =>
    return const (← declName.deepCopy) (← us.mapM Level.deepCopy)
  | app fn arg => return app (← fn.deepCopy) (← arg.deepCopy)
  | lam binderName binderType body binderInfo =>
    return lam (← binderName.deepCopy) (← binderType.deepCopy)
      (← body.deepCopy) binderInfo.deepCopy
  | forallE binderName binderType body binderInfo =>
    return forallE (← binderName.deepCopy) (← binderType.deepCopy)
      (← body.deepCopy) binderInfo.deepCopy
  | letE declName type value body nondep =>
    return letE (← declName.deepCopy) (← type.deepCopy)
      (← value.deepCopy) (← body.deepCopy) nondep.deepCopy
  | lit l => return lit (← l.deepCopy)
  | mdata data expr =>
    return mdata (← data.deepCopy) (← expr.deepCopy)
  | proj typeName idx struct =>
    return proj (← typeName.deepCopy) (← idx.deepCopy)
      (← struct.deepCopy)

def Lean.ReducibilityHints.deepCopy : ReducibilityHints → ReducibilityHints
| .opaque => .opaque
| .abbrev => .abbrev
| .regular n => .regular (.ofNat n.toNat)
def Lean.DefinitionSafety.deepCopy : DefinitionSafety → DefinitionSafety
| .unsafe => .unsafe
| .safe => .safe
| .partial => .partial
unsafe
def Lean.RecursorRule.deepCopy (r : RecursorRule) : M RecursorRule :=
  return {
    ctor := (← r.ctor.deepCopy)
    nfields := (← r.nfields.deepCopy)
    rhs := (← r.rhs.deepCopy) }

unsafe
def Lean.ConstantVal.deepCopy (val : ConstantVal) : M ConstantVal :=
  return {
    name := ← val.name.deepCopy
    levelParams := ← val.levelParams.mapM Name.deepCopy
    type := ← val.type.deepCopy }

unsafe
def Lean.AxiomVal.deepCopy (val : AxiomVal) : M AxiomVal := return {
  (← val.toConstantVal.deepCopy) with
  isUnsafe := val.isUnsafe.deepCopy }
unsafe
def Lean.DefinitionVal.deepCopy (val : DefinitionVal) : M DefinitionVal :=
  return {
    (← val.toConstantVal.deepCopy) with
    value := ← val.value.deepCopy,
    hints := val.hints.deepCopy,
    safety := val.safety.deepCopy,
    all := ← val.all.mapM Name.deepCopy }
unsafe
def Lean.TheoremVal.deepCopy (val : TheoremVal) : M TheoremVal := return {
  (← val.toConstantVal.deepCopy) with
  value := ← val.value.deepCopy,
  all := ← val.all.mapM Name.deepCopy }
unsafe
def Lean.OpaqueVal.deepCopy (val : OpaqueVal) : M OpaqueVal := return {
  (← val.toConstantVal.deepCopy) with
  value := ← val.value.deepCopy,
  isUnsafe := val.isUnsafe.deepCopy
  all := ← val.all.mapM Name.deepCopy }
unsafe
def Lean.QuotVal.deepCopy (val : QuotVal) : M QuotVal := return {
  (← val.toConstantVal.deepCopy) with
  kind := match val.kind with
  | .type => .type
  | .ctor => .ctor
  | .lift => .lift
  | .ind => .ind }
unsafe
def Lean.InductiveVal.deepCopy (val : InductiveVal) : M InductiveVal :=
  return {
    (← val.toConstantVal.deepCopy) with
    numParams := (← val.numParams.deepCopy)
    numIndices := (← val.numIndices.deepCopy)
    all := ← val.all.mapM Name.deepCopy
    ctors := ← val.ctors.mapM Name.deepCopy
    numNested := (← val.numNested.deepCopy)
    isRec := val.isRec.deepCopy
    isUnsafe := val.isUnsafe.deepCopy
    isReflexive := val.isReflexive.deepCopy }
unsafe
def Lean.ConstructorVal.deepCopy (val : ConstructorVal) : M ConstructorVal :=
  return {
    (← val.toConstantVal.deepCopy) with
    induct := ← val.induct.deepCopy
    cidx := (← val.cidx.deepCopy)
    numParams := (← val.numParams.deepCopy)
    numFields := (← val.numFields.deepCopy)
    isUnsafe := val.isUnsafe.deepCopy }
unsafe
def Lean.RecursorVal.deepCopy (val : RecursorVal) : M RecursorVal :=
  return {
    (← val.toConstantVal.deepCopy) with
    all := ← val.all.mapM Name.deepCopy
    numParams := (← val.numParams.deepCopy)
    numIndices := (← val.numIndices.deepCopy)
    numMotives := (← val.numMotives.deepCopy)
    numMinors := (← val.numMinors.deepCopy)
    rules := ← val.rules.mapM RecursorRule.deepCopy
    k := val.k.deepCopy
    isUnsafe := val.isUnsafe.deepCopy }

unsafe
def Lean.ConstantInfo.deepCopy : ConstantInfo → M ConstantInfo
| axiomInfo val => axiomInfo <$> val.deepCopy
| defnInfo val => defnInfo <$> val.deepCopy
| thmInfo val => thmInfo <$> val.deepCopy
| opaqueInfo val => opaqueInfo <$> val.deepCopy
| quotInfo val => quotInfo <$> val.deepCopy
| inductInfo val => inductInfo <$> val.deepCopy
| ctorInfo val => ctorInfo <$> val.deepCopy
| recInfo val => recInfo <$> val.deepCopy

unsafe
def Lean.ModuleData.deepCopy.impl (m : ModuleData) : ModuleData :=
  StateT.run' (s := {}) <| (return {
    isModule := m.isModule
    imports := ← Array.ofFnM
      (fun i : Fin m.imports.size ↦ m.imports[i].deepCopy)
    constNames := ← Array.ofFnM
      (fun i : Fin m.constNames.size ↦ m.constNames[i].deepCopy)
    constants := ← Array.ofFnM
      (fun i : Fin m.constants.size ↦ m.constants[i].deepCopy)
    extraConstNames := ← Array.ofFnM
      (fun i : Fin m.extraConstNames.size ↦ m.extraConstNames[i].deepCopy)
    entries := ← Array.ofFnM
      (fun i : Fin m.entries.size ↦
        let (name, subEntries) := m.entries[i]
        return ( ← name.deepCopy, Array.ofFn
          (fun j : Fin subEntries.size ↦ subEntries[j]) ) )
          -- we resign to sanitize the `EnvExtensionEntry`
          -- since it has not public API to be rebuilt
  } : M ModuleData)

@[implemented_by Lean.ModuleData.deepCopy.impl]
def Lean.ModuleData.deepCopy (m : ModuleData) := m
