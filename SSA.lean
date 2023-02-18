import Mathlib.Data.Int.Basic

inductive Test where
  | aa : Int → Test
  | bb : Nat →  Nat → Test

open Std 

namespace AST

/-
Kinds of values. We must have 'pair' to take multiple arguments.
-/
inductive Kind where
| int : Kind
| float : Kind
| pair : Kind -> Kind -> Kind
| unit: Kind
deriving Inhabited, DecidableEq, BEq

instance : ToString Kind where
  toString k := 
    let rec go : Kind →String  
    | .int => "int"
    | .float => "float"
    | .unit => "unit"
    | .pair p q => s!"({go p}, {go q})"
    go k

-- A binding of 'name' with kind 'Kind'
structure Var where
  name : String
  kind : Kind
deriving Inhabited, DecidableEq, BEq

instance : ToString Var where 
  toString x := "%" ++ x.name ++ ":" ++ toString x.kind 

def Var.unit : Var := { name := "_", kind := .unit }

-- compile time constant values.
inductive Const where
| int: Int → Const
| float: Float → Const 
| unit: Const
| pair: Const → Const → Const
deriving BEq 

instance : ToString Const where
  toString :=
    let rec go : Const → String  
    | .int i => toString i
    | .float f => toString f
    | .unit => "()"
    | .pair p q => s!"({go p}, {go q})"
    go

-- Tag for variants of Op/Region hybrid
inductive OR: Type
| O -- Single Op
| Os -- Multiple Ops
| R -- Single Region
| Rs -- Multiple Regions

-- Tagged expressiontrees
inductive Expr: OR -> Type where
| opsone: Expr .O -> Expr .Os -- terminator in a sequence of Ops
| opscons: Expr .O -> Expr .Os -> Expr .Os -- cons cell 'op :: ops'
| regionsnil : Expr .Rs -- empty sequence of regions
| regionscons: Expr .R -> Expr .Rs -> Expr .Rs -- cons cell 'region :: regions'
| op (ret : Var)
   (name : String)
   (arg : Var)
   (regions : Expr .Rs)
   (const: Const): Expr .O -- '%ret:retty = 'name'(%var:varty) [regions*] {const}'
| tuple (ret: String) (a1 a2: Var): Expr .O -- %out = tuple (%v1, %v2)
| region (arg : Var) (ops : Expr .Os): Expr .R -- '{ ^entry(arg:argty) ops* }'

abbrev Op := Expr .O
abbrev Region := Expr .R
abbrev Regions := Expr .Rs
abbrev Ops := Expr .Os
  
def Op.Ret : Op → Var
| .op ret _ _ _ _ => ret 
| .tuple retname arg1 arg2 => 
   { name := retname,
     kind := .pair arg1.kind arg2.kind : Var}

def Regions.isEmpty: Regions → Bool
| .regionsnil => True
| .regionscons _ _ => False


def Expr.format : Expr k → Format 
| .opsone o => o.format
| .opscons o os => o.format ++ .line ++ os.format
| .regionsnil => Format.nil
| .regionscons r rs => r.format ++ .line ++ rs.format
| .op ret name arg rs const => 
    let constfmt : Format := 
      if const == .unit then ""
      else "{" ++ toString const ++ "}"
    let argfmt : Format :=
      if arg == Var.unit then ""
      else "(" ++ toString arg ++ ")"
    let rsfmt : Format := 
      if Regions.isEmpty rs then ""
      else (Format.nest 1 <| "[" ++ .line ++ Expr.format rs) ++ "]"
    .text (toString ret ++ " = " ++ name) ++ 
    argfmt ++ rsfmt ++ constfmt
| .tuple ret a1 a2 => 
    .text <|
      "%" ++ toString ret ++ " = " ++ 
      "(" ++ toString a1 ++ ", " ++ toString a2 ++ ")"
| .region arg ops => 
    let argfmt : Format :=
    if arg == Var.unit then "" else "^(" ++ toString arg ++ ")"
    "{" ++ argfmt ++ 
      Format.nest 2 (.line ++ ops.format) ++ .line ++ "}"
instance ⦃k: OR⦄: ToFormat (Expr k) where
  format := Expr.format

instance : ToString (Expr k) where
   toString := Format.pretty ∘ format



-- Lean type that corresponds to kind.
@[reducible, simp]
def Kind.eval: Kind -> Type
| .int => Int
| .unit => Unit
| .float => Float
| .pair p q => p.eval × q.eval

end AST

section Semantics
open AST

-- A kind and a value of that kind.
structure Val where
  kind: Kind
  val: kind.eval

instance : BEq Val where
  beq a b := 
    let rec go a b := 
    match a, b with
    | {kind := .int, val := a}, {kind := .int, val := b} => a == b
    | {kind := .float, val := a}, {kind := .float, val := b} => a == b
    | {kind := .unit, val := a}, {kind := .unit, val := b} => a == b
    | {kind := .pair p q, val := ⟨a, a'⟩}, {kind := .pair r s, val := ⟨b, b'⟩ } => 
      go ⟨p, a⟩ ⟨r, b⟩ && go ⟨q, a'⟩ ⟨s, b'⟩
    | _, _ => False
    go a b
 
def Val.unit : Val := { kind := Kind.unit, val := () }

def Val.toString (v: Val): String :=
  match v  with
  | {kind := .int, val := val } => 
      let S : ToString Int := inferInstance
      S.toString val
  | {kind := .float, val := val } => 
      let S : ToString Float := inferInstance
      S.toString val
  | {kind := .unit, val := () } => "()"
  | {kind := .pair p q, val := (x, y) } => 
      let xstr := Val.toString ({ kind := p, val := x})
      let ystr := Val.toString { kind := q, val := y}
      s!"({xstr}, {ystr})"

instance : ToString Val where
  toString := Val.toString

-- The retun value of an SSA operation, with a name, kind, and value of that kind.
structure NamedVal extends Val where
  name : String  
deriving BEq

def NamedVal.toString (nv: NamedVal): String :=
 s!"{nv.name} := {Val.toString nv.toVal}"


instance : ToString NamedVal where
  toString := NamedVal.toString

-- Given a 'Var' of kind 'kind', and a value of type 〚kind⟧, build a 'Val'
def AST.Var.toNamedVal (var: Var) (value: var.kind.eval): NamedVal := 
 { kind := var.kind, val := value, name := var.name }

def NamedVal.var (nv: NamedVal): Var :=
  { name := nv.name, kind := nv.kind }

-- Well typed environments; cons cells of
-- bindings of variables to values of type ⟦var.kind⟧
inductive Env where
| empty: Env
| cons (var: Var) (val: var.kind.eval) (rest: Env): Env 


abbrev ErrorKind := String
abbrev TopM (α : Type) : Type := ReaderT Env (Except ErrorKind) α

def Env.set (var: Var) (val: var.kind.eval): Env → Env
| env => (.cons var val env)

def Env.get (var: Var): Env → TopM var.kind.eval  
| .empty => Except.error s!"unknown var {var.name}"
| .cons var' val env' => 
    if H : var = var'
    then pure (H ▸ val) 
    else env'.get var 

def ReaderT.get [Monad m]: ReaderT ρ m ρ := fun x => pure x
def ReaderT.withEnv [Monad m] (f: ρ → ρ) (reader: ReaderT ρ m α): ReaderT ρ m α :=
  reader ∘ f 

def TopM.get (var: Var): TopM var.kind.eval := ReaderT.get >>= Env.get var
def TopM.set (nv: NamedVal)  (k: TopM α): TopM α := 
  ReaderT.withEnv (Env.set nv.var nv.val) k

def TopM.error (e: ErrorKind) : TopM α := Except.error e

def Val.cast (val: Val) (t: Kind): TopM t.eval :=
  if H : val.kind = t
  then pure (H ▸ val.val)
  else TopM.error s!"mismatched type {val.kind} ≠ {t}"

-- Runtime denotation of an Op, that has evaluated its arguments,
-- and expects a return value of type ⟦retkind⟧ 
structure Op' where
  name : String
  argval : Val := ⟨.unit, ()⟩
  regions: List (Val → TopM NamedVal) := []
  const: Const := .unit
  retkind: Kind 

instance : ToString Op' where
  toString x := 
    x.name ++ "(" ++ toString x.argval ++ ")" ++
    " [" ++ "#" ++ toString x.regions.length ++ "]" ++
    " {" ++ toString x.const ++ "}" ++ " → " ++ toString x.retkind

@[reducible]
def AST.OR.denoteType: OR -> Type
| .O => TopM NamedVal
| .Os => TopM NamedVal
| .R => Val → TopM NamedVal
| .Rs => List (Val → TopM NamedVal) -- TODO: is 'List' here correct?


def AST.Expr.denote {kind: OR}
 (sem: (o: Op') → TopM (o.retkind.eval)): Expr kind → kind.denoteType 
| .opsone o => AST.Expr.denote (kind := .O) sem o
| .opscons o os => do
    let retv ← AST.Expr.denote (kind := .O) sem o
    TopM.set retv (os.denote sem)
| .regionsnil => []
| .regionscons r rs => r.denote sem :: (rs.denote sem)
| .tuple ret arg1 arg2 => do
   let val1 ←TopM.get arg1
   let val2 ← TopM.get arg2
   return { name := ret,
            kind := .pair arg1.kind arg2.kind,
            val := (val1, val2)
          } -- build a pair
| .op ret name arg rs const => do 
    let val ← TopM.get arg 
    let op' : Op' :=
      { name := name
      , argval := ⟨arg.kind, val⟩
      , regions := rs.denote sem
      , const := const
      , retkind := ret.kind }
    let out ← sem op'
    return ret.toNamedVal out
| .region arg ops => fun val => do
    -- TODO: improve dependent typing here
    let val' ← val.cast arg.kind
    TopM.set (arg.toNamedVal val') (ops.denote sem)

def runRegion (sem : (o: Op') → TopM o.retkind.eval) (expr: AST.Expr .R)
(env :  Env := Env.empty)
(arg : Val := Val.unit) : Except ErrorKind NamedVal := 
  (expr.denote sem arg).run env


end Semantics

namespace DSL
open AST

declare_syntax_cat dsl_op
declare_syntax_cat dsl_type
declare_syntax_cat dsl_ops
declare_syntax_cat dsl_region
declare_syntax_cat dsl_var
declare_syntax_cat dsl_const
declare_syntax_cat dsl_kind

syntax sepBy1(ident, "×") :dsl_kind
syntax "%"ident ":" dsl_kind : dsl_var
syntax dsl_var "="
      str
      ("(" dsl_var ")")?
      ("[" dsl_region,* "]")?
      ("{" dsl_const "}")? ";": dsl_op
syntax "%" ident "="  "(" dsl_var "," dsl_var ")" ";": dsl_op
syntax num : dsl_const 
syntax "{" ("^(" dsl_var "):")?  dsl_op dsl_op*  "}" : dsl_region
syntax "[dsl_op|" dsl_op "]" : term 
syntax "[dsl_region|" dsl_region "]" : term 
syntax "[dsl_var|" dsl_var "]" : term
syntax "[dsl_kind|" dsl_kind "]" : term
syntax "[dsl_const|" dsl_const "]" : term 


@[simp]
def AST.Ops.fromList: Op → List Op → Ops
| op, [] => .opsone op
| op, op'::ops => .opscons op (AST.Ops.fromList op' ops)

@[simp]
def AST.Regions.fromList: List Region → Regions
| [] => .regionsnil
| r :: rs => .regionscons r (AST.Regions.fromList rs)

open Lean Macro in 
def parseKind (k: TSyntax `ident) : MacroM (TSyntax `term) := 
  match k.getId.toString with 
  | "int" => `(AST.Kind.int)
  | unk => (throwErrorAt k s!"unknown kind '{unk}'")


open Lean Macro in 
macro_rules
| `([dsl_kind| $[ $ks ]×* ]) => do
    if ks.isEmpty 
    then `(AST.Kind.unit)
    else 
      let mut out ← parseKind ks[0]!
      for k in ks.pop do
        let cur ← parseKind k
        out ← `(AST.Kind.pair $out $cur) 
      return out

macro_rules
| `([dsl_var| %$name:ident : $kind:dsl_kind]) => do 
    `({ name := $(Lean.quote name.getId.toString),
        kind := [dsl_kind| $kind] : Var})

macro_rules
| `([dsl_region| { $[ ^( $arg:dsl_var ): ]? $op $ops* } ]) => do
   let op_term ← `([dsl_op| $op])
   let ops_term ← ops.mapM (fun op => `([dsl_op| $op ]))
   let ops ← `(AST.Ops.fromList $op_term [ $ops_term,* ])
   match arg with 
   | .none => `(Expr.region Var.unit $ops)
   | .some arg => do
      let arg_term ← `([dsl_var| $arg ])
      `(Expr.region $arg_term $ops)

macro_rules
| `([dsl_const| $x:num ]) => `(Const.int $x)

open Lean Syntax in 
macro_rules
| `([dsl_op| $res:dsl_var = $name:str
      $[ ( $arg:dsl_var ) ]?
      $[ [ $rgns,* ] ]? 
      $[ { $const } ]?
      ;
      ]) => do
      let res_term ← `([dsl_var| $res])
      let arg_term ← match arg with 
          | .some arg => `([dsl_var| $arg])
          | .none => `(AST.Var.unit)
      let name_term := Lean.quote name.getString
      let rgns_term ← match rgns with
        | .none => `(.regionsnil)
        | .some rgns => 
           let rgns ← rgns.getElems.mapM (fun stx => `([dsl_region| $stx]))
           `(AST.Regions.fromList [ $rgns,* ])
      let const_term ←
        match const with
        | .none => `(Const.unit)
        | .some c => `([dsl_const| $c])
      `(Expr.op $res_term $name_term $arg_term $rgns_term $const_term)

macro_rules
| `([dsl_op| %$res:ident = ( $arg1:dsl_var , $arg2:dsl_var) ; ]) => do
    let res_term := Lean.quote res.getId.toString
    let arg1_term ← `([dsl_var| $arg1 ])
    let arg2_term ← `([dsl_var| $arg2 ])
    `(Expr.tuple $res_term $arg1_term $arg2_term)

def eg_kind_int := [dsl_kind| int]
#reduce eg_kind_int

def eg_var : AST.Var := [dsl_var| %y : int]
#reduce eg_var
end DSL

namespace Arith
def sem: (o: Op') → TopM (o.retkind.eval)
| { name := "constant",
    const := .int x,
    retkind := .int} => return x 
| { name := "add",
    retkind := .int,
    argval := ⟨.pair .int .int, (x, y)⟩ } => 
      return (x + y)
| { name := "sub",
    retkind := .int,
    argval := ⟨.pair .int .int, (x, y)⟩ } => 
      return (x - y)

| op => TopM.error s!"unknown op: {op}"

def eg_region_sub :=
 [dsl_region| {
   %one : int = "constant" {1};
   %two : int = "constant" {2};
   %t = (%one : int , %two : int);
   %x : int = "sub"(%t : int × int);
 }]
#reduce eg_region_sub


end Arith

namespace Scf

def repeatM: Nat → (Val → TopM Val) → Val → TopM Val
| 0, _ => pure
| .succ n, f => f >=> repeatM n f
 

def sem: (o: Op') → TopM (o.retkind.eval) 
| { name := "if",
    argval := ⟨.int, cond⟩,
    regions := [rthen, relse],
    retkind := .int -- hack: we assume that we always return ints.
  } => do 
    let rrun := if cond ≠ 0 then rthen else relse
    let v ← rrun Val.unit
    v.cast .int
| { name := "twice",
    regions := [r],
    retkind := .int
  } => do
    let v ← r Val.unit
    let w ← r Val.unit -- run a region twice, check that it is same as running once.
    w.cast .int  
| { name := "for",
    regions := [r],
    retkind := .int,
    argval := ⟨.pair .int .int, ⟨init, niters⟩⟩
  } => do
    let niters : Nat := 
      match niters with
      | .ofNat n => n 
      | _ => 0
    let loopEffect := (fun v => NamedVal.toVal <$> (r v)) 
    let w ← repeatM niters loopEffect ⟨.int, init⟩
    w.cast .int 
| op => TopM.error s!"unknown op {op}"
end Scf

namespace Combine
def combineSem: (s1 s2: (o: Op') → TopM o.retkind.eval) → 
    (x: Op') → TopM x.retkind.eval := 
  fun s1 s2 o => 
     let f1 := (s1 o)
     let f2 := (s2 o)
     fun env => (f1 env).orElseLazy (fun () => f2 env) 

end Combine

namespace Examples
open AST 
def eg_arith_shadow : Region := [dsl_region| {
  %x : int = "constant"{0};
  %x : int = "constant"{1};
  %x : int = "constant"{2};
  %x : int = "constant"{3};
  %x : int = "constant"{4};
}]

def eg_scf_ite_true : Region := [dsl_region| {
  %cond : int = "constant"{1};
  %out : int = "if" (%cond : int) [{
    %out_then : int = "constant"{42};
  }, {
    %out_else : int = "constant"{0};
  }];
}]

def eg_scf_ite_false : Region := [dsl_region| {
  %cond : int = "constant"{0};
  %out : int = "if" (%cond : int) [{
    %out_then : int = "constant"{42};
  }, {
    %out_else : int = "constant"{0};
  }];
}]

def eg_scf_run_twice : Region := [dsl_region| {
  %x : int = "constant"{41};
  %x : int = "twice" [{
      %one : int = "constant"{1};
      %xone = (%x : int, %one : int);
      %x : int = "add"(%xone : int × int);
  }];
}]

def eg_scf_well_scoped_1 : Region := [dsl_region| {
  %x : int = "constant"{41};
  %one : int = "constant"{1}; -- one is outside.
  %x : int = "twice" [{
      %xone = (%x : int, %one : int); -- one is accessed here.
      %x : int = "add"(%xone : int × int);
  }];
}]

def eg_scf_ill_scoped_1 : Region := [dsl_region| {
  %x : int = "constant"{41};
  %x : int = "twice" [{
      %y : int = "constant"{42};
  }];
  -- %y should NOT be accessible here
  %out = (%y : int, %y : int);
}]

def eg_scf_for: Region := [dsl_region| {
  %x : int = "constant"{10};  -- 10 iterations
  %init : int = "constant"{32}; -- start value
  %xinit = (%x : int, %init : int);
  %out : int = "for"(%xinit : int × int)[{
    ^(%xcur : int):
      %one : int = "constant"{1};
      %xcur_one = (%xcur : int, %one : int);
      %xnext : int = "add"(%xcur_one : int × int);
  }];
}]



end Examples

namespace Test
def runRegionTest : 
  (sem: (o: Op') → TopM o.retkind.eval) →
  (r: AST.Region) → 
  (expected: NamedVal) →
  (arg: Val := Val.unit ) →
  (env: Env := Env.empty) → IO Bool := 
  fun sem r expected arg env => do
    IO.println r
    let v? := (r.denote sem arg).run env
    match v? with 
    | .ok v => 
      if v == expected
      then
        IO.println s!"{v}. OK"; return True
      else 
        IO.println s!"ERROR: computed '{v}', expected '{expected}'."
        return False
    | .error e => 
      IO.println s!"ERROR: '{e}'. Expected '{expected}'."
      return False

def runRegionTestXfail : 
  (sem: (o: Op') → TopM o.retkind.eval) →
  (r: AST.Region) → 
  (arg: Val := Val.unit ) →
  (env: Env := Env.empty) → IO Bool := 
  fun sem r arg env => do
    IO.println r
    let v? := (r.denote sem arg).run env
    match v? with 
    | .ok v => 
        IO.println s!"ERROR: expected failure, but succeeded with '{v}'."; 
        return False
    | .error e => 
      IO.println s!"OK: Succesfully xfailed '{e}'."
      return True

end Test


open Arith Scf Combine DSL Examples Test in 
def main : IO UInt32 := do 
  let tests := 
  [runRegionTest 
    (sem := Arith.sem)
    (r := eg_region_sub)
    (expected := { name := "x", kind := .int, val := -1}),
  runRegionTest 
    (sem := Arith.sem)
    (r := eg_arith_shadow)
    (expected := { name := "x", kind := .int, val := 4}),
   runRegionTest 
    (sem := Combine.combineSem Scf.sem Arith.sem)
    (r := eg_scf_ite_true)
    (expected := { name := "out", kind := .int, val := 42}),
  runRegionTest 
    (sem := Combine.combineSem Scf.sem Arith.sem)
    (r := eg_scf_ite_false)
    (expected := { name := "out", kind := .int, val := 0}),
  runRegionTest 
    (sem := Combine.combineSem Scf.sem Arith.sem)
    (r := eg_scf_run_twice)
    (expected := { name := "x", kind := .int, val := 42}),
  runRegionTest 
    (sem := Combine.combineSem Scf.sem Arith.sem)
    (r := eg_scf_well_scoped_1)
    (expected := { name := "x", kind := .int, val := 42}),
  runRegionTestXfail
    (sem := Combine.combineSem Scf.sem Arith.sem)
    (r := eg_scf_ill_scoped_1),
  runRegionTest 
    (sem := Combine.combineSem Scf.sem Arith.sem)
    (r := eg_scf_for)
    (expected := { name := "out", kind := .int, val := 42})]
  let mut total := 0
  let mut correct := 0
  for t in tests do
    total := total + 1
    IO.println s!"---Test {total}---"
    let pass? ← t 
    if pass? then correct := correct + 1
  IO.println "---"
  IO.println s!"Tests: {correct} successful/{total}"
  return (if correct == total then 0 else 1)