import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.Lemmas
open Mathlib
open Std 
open Int
open Nat

namespace AST


/-
Kinds of values. We must have 'pair' to take multiple arguments.
-/
inductive Kind where
| int : Kind
| nat: Kind 
| float : Kind
| tensor1d: Kind
| tensor2d: Kind
| pair : Kind -> Kind -> Kind
| unit: Kind
deriving Inhabited, DecidableEq, BEq

-- A binding of 'name' with kind 'Kind'
structure Var where
  name : String
  kind : Kind
deriving Inhabited, DecidableEq, BEq

@[match_pattern]
def Var.unit : Var := { name := "_", kind := .unit }

-- Tag for variants of Op/Region hybrid
inductive OR: Type
| O -- Single Op
| Os -- Multiple Ops

-- Tagged expressiontrees
inductive Expr: OR -> Type where
| opsone: Expr .O -> Expr .Os -- terminator in a sequence of Ops
| opscons: Expr .O -> Expr .Os -> Expr .Os -- cons cell 'op :: ops'
| op (ret : Var)
   (name : String)
   (arg : List Var): Expr .O -- '%ret:retty = 'name'(%var:varty) [regions*] {const}'

abbrev Op := Expr .O
abbrev Ops := Expr .Os

def Op.mk (ret: Var := Var.unit)
  (name: String)
  (arg: Var := Var.unit) : Op := Expr.op ret name [arg]

def Op.Ret : Op → Var
| .op ret _ _ => ret 

-- Lean type that corresponds to kind.
@[reducible, simp]
def Kind.eval: Kind -> Type
| .int => Int
| .nat => Nat
| .unit => Unit
| .float => Float
| .tensor1d => Nat → Int
| .tensor2d => Nat → Nat → Int  
| .pair p q => p.eval × q.eval

end AST

section Semantics
open AST

-- A kind and a value of that kind.
structure Val where
  kind: Kind
  val: kind.eval

 
def Val.unit : Val := { kind := Kind.unit, val := () }

-- The retun value of an SSA operation, with a name, kind, and value of that kind.
structure NamedVal extends Val where
  name : String  


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

inductive OpM (a: Type) where 
| Ret: a →OpM a
| Get: Var → (NamedVal → OpM a) → OpM a
| Set: (v: NamedVal) → (rest: OpM a) → OpM a   
-- | RunRegion: (List Val → OpM a) → OpM a
| Error: String → OpM a 

def OpM.bind: OpM α → (α → OpM β) → OpM β
| .Ret a, f => f a
| .Error s, _f => .Error s
| .Get v k, f => .Get v (fun w => (k w).bind f)
| .Set v rest, f => .Set v (rest.bind f)
-- | .RunRegion g args, f=> .RunRegion (fun a => (g a).bind f) args

instance : Monad OpM where
  pure := .Ret
  bind := OpM.bind

abbrev ErrorKind := String
abbrev TopM (α : Type) : Type := StateT Env (Except ErrorKind) α


def Env.set (var: Var) (val: var.kind.eval): Env → Env
| env => (.cons var val env)

def Env.get (var: Var): Env → Except ErrorKind NamedVal 
| .empty => Except.error s!"unknown var {var.name}"
| .cons var' val env' => 
    if H : var = var'
    then pure <| var.toNamedVal (H ▸ val) 
    else env'.get var 

def TopM.get (var: Var): TopM NamedVal := do 
  let e ← StateT.get 
  Env.get var e
def OpM.get (var: Var): OpM NamedVal := OpM.Get var pure

def TopM.set (nv: NamedVal)  (k: TopM α): TopM α := do 
  let e ← StateT.get
  let e' := Env.set nv.var nv.val e
  StateT.set e'
  let out ← k
  StateT.set e 
  return out 
def OpM.set (nv: NamedVal)  (k: OpM α): OpM α := OpM.Set nv k
def OpM.set' (nv: NamedVal) : OpM Unit := OpM.Set nv (pure ())

def TopM.error (e: ErrorKind) : TopM α := Except.error e
def OpM.error (e: ErrorKind): OpM α := OpM.Error e

def OpM.toTopM: OpM a → TopM a
| OpM.Ret a => return a
| OpM.Error e => TopM.error e
| OpM.Get var k => do 
    let out ← TopM.get var
    (k out).toTopM 
| OpM.Set nv rest => do
   TopM.set nv (rest.toTopM)
-- | OpM.RunRegion k args =>  (k args).toTopM

def Val.cast (val: Val) (t: Kind): OpM t.eval :=
  if H : val.kind = t
  then pure (H ▸ val.val)
  else OpM.error s!"mismatched type "

-- Runtime denotation of an Op, that has evaluated its arguments,
-- and expects a return value of type ⟦retkind⟧ 
inductive Op' where
| mk
  (name : String)
  (argval : List Val)

def Op'.name: Op' → String 
| .mk name argval => name 

def Op'.argval: Op' → List Val 
| .mk name argval => argval


@[reducible]
def AST.OR.denoteType: OR -> Type
| .O => OpM NamedVal
| .Os => OpM NamedVal

def AST.Expr.denote {kind: OR}
 (sem: (o: Op') → OpM Val): Expr kind → kind.denoteType 
| .opsone o => AST.Expr.denote (kind := .O) sem o
| .opscons o os => do
    let retv ← AST.Expr.denote (kind := .O) sem o
    OpM.set retv (os.denote sem)
| .op ret name args  => do 
    let vals ← args.mapM OpM.get
    let op' : Op' := .mk
      name
      (vals.map NamedVal.toVal)
    let out ← sem op'
    if ret.kind = out.kind
    then return { name := ret.name,  kind := out.kind, val := out.val : NamedVal }
    else OpM.error "unexpected return kind '{}', expected {}"

def runOps (sem : (o: Op') → OpM Val) (expr: AST.Expr .Os)
(env :  Env := Env.empty) : Except ErrorKind (NamedVal × Env) := 
  (expr.denote sem).toTopM.run env


end Semantics

namespace Arith

set_option pp.all true in 
def sem: (o: Op') → OpM Val
| .mk "float" [] => return ⟨.float, x+1⟩
| .mk "float2" [⟨.float, x⟩] => return ⟨.float, x + x⟩
| .mk "int2" [⟨.int, x⟩] => return ⟨.int, x + x⟩
| .mk "nat2" [⟨.nat, x⟩] => return ⟨.nat, x + x⟩
| .mk "add" [⟨.int, x⟩, ⟨.int, y⟩]   => 
      return ⟨.int, (x + y)⟩
| .mk "sub" [⟨.int, x⟩, ⟨.int, y⟩] => 
      return ⟨.int, (x - y)⟩
| .mk "tensor1d" [⟨.tensor1d, t⟩, ⟨.nat, ix⟩] => 
    let i := t ix 
    return ⟨.int, i + i⟩
| .mk "tensor2d" [⟨.tensor2d, t⟩, ⟨.int, i⟩, ⟨.nat, j⟩] => 
    let i := t 0 0
    let j := t 1 1
    return ⟨.int, i + i⟩
| op => OpM.error s!"unknown op"


open AST in 
def eg_region_sub : Ops := 
  .opsone (Op.mk (name := "float") )
#reduce eg_region_sub

open AST in 
theorem Fail: runOps sem eg_region_sub   = .ok output  := by {
  simp[eg_region_sub];
  -- ERROR:
  -- tactic 'simp' failed, nested error:
  -- (deterministic) timeout at 'whnf', maximum number of heartbeats (200000) has been reached (use 'set_option maxHeartbeats <num>' to set the limit)
  simp[sem]; -- SLOW, but not timeout level slow
  simp[runRegion];
  simp[StateT.run]
  simp[Expr.denote];
  simp[bind];
  simp[StateT.bind];
}

end Arith


def main : IO Unit := return ()