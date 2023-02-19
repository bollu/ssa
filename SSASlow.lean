/-
Kinds of values.
-/
inductive Kind where
| kind_a : Kind
| kind_b : Kind
| kind_c : Kind 
| kind_d : Kind
| kind_e : Kind
| kind_f : Kind
deriving Inhabited, DecidableEq, BEq

def Kind.unit : Kind := .kind_a

inductive Op: Type where
| op (arg : List Kind): Op 

-- Lean type that corresponds to kind.
@[reducible, simp]
def Kind.eval: Kind -> Type
| .kind_a => Int
| .kind_b => Int
| .kind_c => Int
| .kind_d => Int
| .kind_e => Int
| .kind_f => Int

-- A kind and a value of that kind.
structure Val where
  kind: Kind
  val: kind.eval

-- Runtime denotation of an Op, that has evaluated its arguments,
-- and expects a return value of type ⟦retkind⟧ 
inductive Op' where
| mk (name : String) (argval : List Val)

def Op.denote 
 (sem: (o: Op') → Val) : Op  → Val 
| .op _ => 
    let op' : Op' := .mk "x" [⟨.kind_a, 0⟩] 
    let out := sem op'
    { kind := out.kind, val := out.val : Val }

def sem: (o: Op') → Val
| .mk "a" [⟨.kind_a, _⟩] => ⟨.kind_a, 0⟩
| .mk "b" [⟨.kind_a, _⟩] => ⟨.kind_a, 0⟩
| .mk "c" [⟨.kind_a, _⟩] => ⟨.kind_a, 0⟩
| .mk "d" [⟨.kind_a, _⟩] => ⟨.kind_a, 0⟩
| .mk "e" [⟨.kind_a, _⟩] => ⟨.kind_a, 0⟩
| .mk "f" [⟨.kind_a, _⟩] => ⟨.kind_a, 0⟩
| .mk "g" [⟨.kind_a, _⟩] => ⟨.kind_a, 0⟩
| .mk "h" [⟨.kind_a, _⟩] => ⟨.kind_a, 0⟩
| _ => ⟨.kind_a, 0⟩

set_option maxHeartbeats 200000
theorem Fail: (Op.op [Kind.unit]).denote sem = output  := by {
  -- ERROR:
  -- tactic 'simp' failed, nested error:
  -- (deterministic) timeout at 'whnf', maximum number of heartbeats (200000) has been reached (use 'set_option maxHeartbeats <num>' to set the limit)
  
  simp only[sem]; -- SLOW, but not timeout level slow

}