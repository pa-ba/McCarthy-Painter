Module Type Memory.

Parameter adr : Set.

Parameter first : adr.
Parameter next : adr -> adr.



Parameter Mem : Type.

Parameter empty : Mem.
Parameter get : adr -> Mem -> nat.
Parameter set : adr -> nat -> Mem -> Mem.
Parameter free : adr -> Mem -> Mem.
Parameter isFreeFrom : adr -> Mem -> Prop.

Axiom isFreeFrom_free : forall (r : adr) (m : Mem) (n : nat), isFreeFrom r m -> free r (set r n m) = m.

Axiom isFreeFrom_set : forall (r : adr) (m : Mem) (n : nat), isFreeFrom r m  ->  isFreeFrom (next r) (set r n m).

Axiom get_set : forall (r : adr) (m : Mem) (n : nat), get r (set r n m) = n.

Axiom isFreeFrom_first : isFreeFrom first empty.


End Memory.


Inductive lta T n (r : T) : T -> Prop :=
| lea_self : lta T n r (n r)
| lea_next r' : lta T n r r' -> lta T n r (n r').


(* Extended memory model with additional axioms that are only used for
compiling variables. *)

Module Type MemoryExt.
Include Memory.


Axiom get_set' : forall (r : adr) (r' : adr) (m : Mem) (n : nat),
    r <> r' -> get r (set r' n m) = get r m.
                 
Infix "<" := (lta adr next).
Hint Constructors lta.

Axiom next_fresh : forall (r r' : adr), r < r' -> r <> r'.

End MemoryExt.