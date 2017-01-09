(** Calculation of the simple arithmetic language. *)

Require Import Tactics.
Require Export Memory.
Module Arith (mem : Memory).
Import mem.

(** * Syntax *)

Inductive Expr : Set := 
| Val : nat -> Expr 
| Add : Expr -> Expr -> Expr.

(** * Semantics *)

Fixpoint eval (x: Expr) : nat :=
  match x with
    | Val n => n
    | Add x1 x2 => eval x1 + eval x2
  end.

(** * Compiler *)

Inductive Code : Set :=
| LOAD : nat -> Code -> Code
| ADD : adr -> Code -> Code
| STORE : adr -> Code -> Code
| HALT : Code.

Fixpoint comp' (x : Expr) (r : adr) (c : Code) : Code :=
  match x with
  | Val n => LOAD n c
  | Add x1 x2 => comp' x1 r (STORE r (comp' x2 (next r) (ADD r c)))
  end.

Definition comp (x : Expr) : Code := comp' x first HALT.

(** * Virtual Machine *)

Definition Memory : Type := Mem.
Definition Acc : Type := nat.

Definition Conf : Type := Code * Memory * Acc.

Reserved Notation "x ==> y" (at level 80, no associativity).
Inductive VM : Conf -> Conf -> Prop :=
| vm_load n c m a : (LOAD n c , m, a) ==> (c , m, n)
| vm_add c r m a : (ADD r c, m, a) ==> (c, free r m, get r m + a)
| vm_store c r m a : (STORE r c, m, a) ==> (c, set r a m, a)
where "x ==> y" := (VM x y).

(** * Calculation *)

(** Boilerplate to import calculation tactics *)

Module VM <: Preorder.
Definition Conf := Conf.
Definition VM := VM.
End VM.
Module VMCalc := Calculation VM.
Import VMCalc.

(** Specification of the compiler *)

Theorem spec x r c a m :
  freeFrom r m ->
  (comp' x r c, m, a) =>> (c , m, eval x).

(** Setup the induction proof *)

Proof.
  intros.
  generalize dependent c.
  generalize dependent m.
  generalize dependent r.
  generalize dependent a.
  induction x;intros.

(** Calculation of the compiler *)

(** - [x = Val n]: *)

  begin
  (c, m, n).
  <== { apply vm_load }
  (LOAD n c, m, a).
  [].

(** - [x = Add x1 x2]: *)

  begin
    (c, m, eval x1 + eval x2).
  = {rewrite freeFrom_free, get_set}
    (c, free r (set r (eval x1) m), get r (set r (eval x1) m)  + eval x2).
  <== {apply vm_add}
    (ADD r c, set r (eval x1) m, eval x2).
  <<= {apply IHx2; auto using freeFrom_set}
    (comp' x2 (next r) (ADD r c), set r (eval x1) m, eval x1).
  <== {apply vm_store}
    (STORE r (comp' x2 (next r) (ADD r c)), m, eval x1).
  <<= { apply IHx1}
    (comp' x1 r (STORE r (comp' x2 (next r) (ADD r c))), m, a).
  [].
Qed.


(** * Soundness *)
  
(** Since the VM is defined as a small step operational semantics, we
have to prove that the VM is deterministic and does not get stuck in
order to derive soundness from the above theorem. *)


Lemma determ_vm : determ VM.
  intros C C1 C2 V. induction V; intro V'; inversion V'; subst; reflexivity.
Qed.


Theorem sound x a C : (comp x, empty, a) =>>! C -> C = (HALT , empty, eval x).
Proof.
  intros.
  pose (spec x first HALT) as H'. unfold comp in *. pose (determ_trc determ_vm) as D.
  unfold determ in D. eapply D. apply H. split. apply H'. apply freeFrom_first. intro Contra. destruct Contra.
  inversion H0.
Qed.

End Arith.