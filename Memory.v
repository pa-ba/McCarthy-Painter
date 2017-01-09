Module Type Memory.

Parameter adr : Set.

Parameter first : adr.
Parameter next : adr -> adr.



Parameter Mem : Type.

Parameter empty : Mem.
Parameter get : adr -> Mem -> nat.
Parameter set : adr -> nat -> Mem -> Mem.
Parameter free : adr -> Mem -> Mem.
Parameter freeFrom : adr -> Mem -> Prop.

Axiom freeFrom_free : forall (r : adr) (m : Mem) (n : nat), freeFrom r m -> free r (set r n m) = m.

Axiom freeFrom_set : forall (r : adr) (m : Mem) (n : nat), freeFrom r m  ->  freeFrom (next r) (set r n m).

Axiom get_set : forall (r : adr) (m : Mem) (n : nat), get r (set r n m) = n.

Axiom freeFrom_first : freeFrom first empty.




End Memory.