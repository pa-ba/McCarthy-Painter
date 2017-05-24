(** Calculation of the simple arithmetic language. *)

Require Import Tactics.
Require Export Memory.
Module Arith (mem : MemoryExt).
Import mem.

(** * Syntax *)

Inductive var := X | Y | Z.

Inductive Expr : Set :=
| Val : nat -> Expr 
| Add : Expr -> Expr -> Expr
| Var : var -> Expr.

(** * Semantics *)

Definition env := var -> nat.

Fixpoint eval (e : env) (x: Expr) : nat :=
  match x with
    | Val n => n
    | Add x1 x2 => eval e x1 + eval e x2
    | Var v => e v
  end.

(** * Compiler *)

Inductive Code : Set :=
| LOAD : nat -> Code -> Code
| LDA : adr -> Code -> Code
| ADD : adr -> Code -> Code
| STORE : adr -> Code -> Code
| HALT : Code.

Fixpoint comp' (x : Expr) (vars: var -> adr) (r : adr) (c : Code) : Code :=
  match x with
  | Val n => LOAD n c
  | Add x1 x2 => comp' x1  vars r (STORE r (comp' x2 vars (next r) (ADD r c)))
  | Var v => LDA (vars v) c
  end.

Definition mkVars : var -> adr :=
  fun v =>
    match v with
    | X => first
    | Y => next first
    | Z => next (next first)
    end.

Definition firstFresh : adr := next (next (next first)).

Definition mkMem (e : env) : Mem :=
  set (mkVars Z) (e Z) ((set (mkVars Y) (e Y) (set (mkVars X) (e X) empty))).  
  
  
Definition comp (x : Expr) : Code := comp' x mkVars firstFresh HALT.

(** * Virtual Machine *)

Definition Memory : Type := Mem.
Definition Acc : Type := nat.

Definition Conf : Type := (Code * Memory * Acc)%type.

Reserved Notation "x ==> y" (at level 80, no associativity).
Inductive VM : Conf -> Conf -> Prop :=
| vm_load n c m a : (LOAD n c , m, a) ==> (c , m, n)
| vm_add c r m a : (ADD r c, m, a) ==> (c, free r m, get r m + a)
| vm_store c r m a : (STORE r c, m, a) ==> (c, set r a m, a)
| vm_lda c r m a : (LDA r c, m, a) ==> (c, m, get r m)
where "x ==> y" := (VM x y).

(** * Calculation *)

(** Boilerplate to import calculation tactics *)

Module VM <: Preorder.
Definition Conf := Conf.
Definition VM := VM.
End VM.
Module VMCalc := Calculation VM.
Import VMCalc.

Lemma env_fresh (e : env) vars r m
  (Fresh : forall v, vars v < r)
  (Env : forall v, e v = get (vars v) m) v n:
  e v = get (vars v) (set r n m).
Proof.
  rewrite get_set'; auto using next_fresh.
Qed.
  
  
(** Specification of the compiler *)

Theorem spec x r c a m vars e
  (Fresh : forall v, vars v < r)
  (Env : forall v, e v = get (vars v) m):
  freeFrom r m ->
  (comp' x vars r c, m, a) =>> (c , m, eval e x).

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
    (c, m, eval e x1 + eval e x2).
  = {rewrite freeFrom_free, get_set}
    (c, free r (set r (eval e x1) m), get r (set r (eval e x1) m)  + eval e x2).
  <== {apply vm_add}
    (ADD r c, set r (eval e x1) m, eval e x2).
  <<= {apply IHx2; auto using freeFrom_set, env_fresh}
    (comp' x2 vars (next r) (ADD r c), set r (eval e x1) m, eval e x1).
  <== {apply vm_store}
    (STORE r (comp' x2 vars (next r) (ADD r c)), m, eval e x1).
  <<= { apply IHx1}
    (comp' x1 vars r (STORE r (comp' x2 vars (next r) (ADD r c))), m, a).
  [].

(** - [x = Var v]: *)
  
  begin
    (c, m, e v).
  = {rewrite Env}
    (c, m, get (vars v) m).
  <<= {apply vm_lda}
    (LDA (vars v) c , m, a).  
  [].
Qed.


Lemma mkMemEnv (e : env) (v : var) : e v = get (mkVars v) (mkMem e).
Proof.
  destruct v;
  unfold mkMem; simpl;
    repeat first [rewrite get_set' by (apply next_fresh; auto) | rewrite get_set];
    reflexivity.
Qed.

Lemma mkVarsFresh v : mkVars v < firstFresh.
Proof.
  unfold firstFresh. destruct v; simpl; auto.
Qed.

Lemma freeFromFirst e : freeFrom firstFresh (mkMem e).
Proof.
  unfold mkMem. simpl. eauto using freeFrom_first, freeFrom_set.
Qed. 

Theorem spec_top x a e:
  (comp x, mkMem e, a) =>> (HALT , mkMem e, eval e x).
Proof.
  apply spec.
  - apply mkVarsFresh.
  - apply mkMemEnv.
  - apply freeFromFirst.
Qed. 


(** * Soundness *)
  
(** Since the VM is defined as a small step operational semantics, we
have to prove that the VM is deterministic and does not get stuck in
order to derive soundness from the above theorem. *)


Lemma determ_vm : determ VM.
  intros C C1 C2 V. induction V; intro V'; inversion V'; subst; reflexivity.
Qed.


Theorem sound x a C e : (comp x, mkMem e, a) =>>! C -> C = (HALT , mkMem e, eval e x).
Proof.
  intros.
  pose (spec_top x) as H'. unfold comp in *. pose (determ_trc determ_vm) as D.
  unfold determ in D. eapply D. apply H. split. apply H'. intro Contra. destruct Contra.
  inversion H0.
Qed.

End Arith.