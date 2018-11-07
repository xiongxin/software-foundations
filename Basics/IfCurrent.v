Require Export Basics.

Theorem plus_n_O_secondtry' : forall n : nat,
  n = n + 0.
Proof.
  intros n. destruct n as [| n'].
  - (* n = 0 *)
    reflexivity. (* so far so good... *)
  - (* n = S n' *)
    simpl. (* ...but here we are stuck again *)
Abort.


Theorem plus_n_O: forall n: nat,
  n = n + 0 .
Proof.
  intros n.
  induction n as [| n' IHn'].
  (* 0 = 0 + 0 *)
  - reflexivity.
  (* S n' = S n' + 0 *)
  - simpl. rewrite <- IHn'. simpl. simpl. reflexivity.
Qed.

Theorem minus_diag: forall n : nat,
  minus n n = 0 .
Proof.
  intros n.
  induction n as [| n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite -> IHn'. reflexivity.
Qed.

(*Exercise: 2 stars, recommended (basic_induction) *)

Theorem mult_0_r: forall n : nat,
  n * 0 = 0 .
Proof.
  intros n.
  induction n as [|n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite -> IHn'. reflexivity.
Qed.


Theorem plus_n_Sm: forall n m : nat,
  S (n + m) = n + ( S m ) .
Proof.
  intros n m.
  induction n as [|n' IHn'].
  induction m as [|m' IHm'].
  (* S (0 + 0) = 0 + 1 *)
  - simpl. reflexivity.
  (* S (0 + S m') = 0 + S (S m') *)
  - simpl. reflexivity.
  (* S (S n' + m) = S n' + S m *)
  - simpl. rewrite <- IHn'. reflexivity.
Qed.

Theorem plus_comm: forall n m : nat,
  n + m = m + n .
Proof.
  intros n m.
  induction n as [|n' IHn'].
  induction m as [|m' IHm'].
  (* 0 + 0 = 0 + 0 *)
  - simpl. reflexivity.
  (* 0 + S m' = S m' + 0 *)
  - simpl. rewrite <- IHm'. simpl. reflexivity.
  (* 
  n', m: nat
  IHn': n' + m = m + n'  
  S n' + m = m + S n' 
  *)
  - simpl. rewrite -> IHn'. rewrite -> plus_n_Sm. reflexivity.
Qed.

  (*
    1/4
    0 + (0 + 0) = 0 + 0 + 0
    2/4
    0 + (0 + S p') = 0 + 0 + S p'
    3/4
    0 + (S m' + p) = 0 + S m' + p
    4/4
    S n' + (m + p) = S n' + m + p
  *)
Theorem plus_assoc : forall n m p : nat,
  n + ( m + p) = (n + m) + p .
Proof.
  intros n m p.
  induction n as [|n' IHn'].
  induction m as [|m' IHm'].
  induction p as [|p' IHp'].
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl. rewrite -> IHn'. reflexivity.
Qed.













