Require Import Memory.
Require Import ZArith.
Require Import FunctionalExtensionality.
Module LinearMemory <: Memory.
Definition adr := nat.
Definition first := 0.
Definition next := S.


Definition Mem := adr -> nat.

Definition get r (m : Mem) := m r.
Definition set r v (m : Mem) r' :=
  if beq_nat r' r then v else m r'.


Definition empty : Mem := fun _ => 0.

Definition free : adr -> Mem -> Mem :=
  fun r m => set r 0 m.
    
Definition freeFrom : adr -> Mem -> Prop :=
  fun r m => forall r', r <= r' -> m r' = 0.

Lemma freeFrom_free : forall (r : adr) (m : Mem) (n : nat), freeFrom r m -> free r (set r n m) = m.
Proof.
  intros. unfold free, freeFrom, set in *. apply functional_extensionality. intros.
  remember (beq_nat x r) as b. destruct b.
  - symmetry in Heqb. apply beq_nat_true in Heqb. subst. erewrite H;auto.
  - reflexivity.
Qed. 

Lemma freeFrom_set : forall (r : adr) (m : Mem) (n : nat), freeFrom r m  ->  freeFrom (next r) (set r n m).
Proof.
  unfold freeFrom, set, next. intros.  remember (beq_nat r' r) as b. destruct b;symmetry in Heqb.
  - apply beq_nat_true in Heqb. omega.
  - apply beq_nat_false in Heqb. apply H. omega.
Qed. 

Lemma get_set : forall (r : adr) (m : Mem) (n : nat), get r (set r n m) = n.
Proof.
  intros. unfold get, set. rewrite <- beq_nat_refl. reflexivity.
Qed.

Lemma freeFrom_first : freeFrom first empty.
Proof.
  unfold freeFrom, first, empty. auto.
Qed.
End LinearMemory.

Module LinearMemoryExt <: MemoryExt.
Include LinearMemory.

Lemma get_set' : forall (r : adr) (r' : adr) (m : Mem) (n : nat),
    r <> r' -> get r (set r' n m) = get r m.
Proof.
  intros.
  unfold get, set. remember (r =? r') as b. destruct b.
  - symmetry in Heqb. apply beq_nat_true in Heqb. contradiction.
  - reflexivity.
Qed.


Lemma next_fresh : forall (r r' : adr), lta adr next r r' -> r <> r'.
Proof.
  intros. apply Nat.lt_neq.
  intros. induction H; auto.
Qed.

End LinearMemoryExt.  