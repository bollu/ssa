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

inductive Op: Type where
| op (ret : Var)
   (name : String)
   (arg : List Var): Op 


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

def TopM.set (nv: NamedVal)  (k: TopM α): TopM α := do 
  let e ← StateT.get
  let e' := Env.set nv.var nv.val e
  StateT.set e'
  let out ← k
  StateT.set e 
  return out 

def TopM.error (e: ErrorKind) : TopM α := Except.error e

-- Runtime denotation of an Op, that has evaluated its arguments,
-- and expects a return value of type ⟦retkind⟧ 
inductive Op' where
| mk (name : String) (argval : List Val)

def AST.Op.denote 
 (sem: (o: Op') → TopM Val): Op  → TopM NamedVal 
| .op ret name args  => do 
    let vals ← args.mapM TopM.get
    let op' : Op' := .mk name (vals.map NamedVal.toVal)
    let out ← sem op'
    if ret.kind = out.kind
    then return { name := ret.name,  kind := out.kind, val := out.val : NamedVal }
    else TopM.error "unexpected return kind '{}', expected {}"

def runOp (sem : (o: Op') → TopM Val) (Op: AST.Op)
(env :  Env := Env.empty) : Except ErrorKind (NamedVal × Env) := 
  (Op.denote sem).run env


end Semantics

namespace Arith

def sem: (o: Op') → TopM Val
| .mk "float" [⟨.float, x⟩] => return ⟨.float, x+1⟩
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
| op => TopM.error s!"unknown op"


open AST in 
theorem Fail: runOp sem  (Op.op  Var.unit "float" [])   = .ok output  := by {
  -- ERROR:
  -- tactic 'simp' failed, nested error:
  -- (deterministic) timeout at 'whnf', maximum number of heartbeats (200000) has been reached (use 'set_option maxHeartbeats <num>' to set the limit)
  simp[sem]; -- SLOW, but not timeout level slow
  simp[runRegion];
  simp[StateT.run]
  simp[Op.denote];
  simp[bind];
  simp[StateT.bind];
}

end Arith


def main : IO Unit := return ()