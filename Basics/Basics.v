Inductive day : Type :=
  | monday : day
  | tuesday : day
  | wednesday : day
  | thursday : day
  | friday : day
  | saturday : day
  | sunday : day.

Definition next_weekday (d:day) : day :=
  match d with
    | monday => tuesday
    | tuesday => wednesday
    | wednesday => thursday
    | thursday => friday
    | friday => monday
    | saturday => monday
    | sunday => monday
  end.  

Example test_next_weekday:
  (next_weekday (next_weekday saturday)) = tuesday.

Proof. simpl. reflexivity. Qed.

(* Booleans type *)  

Inductive bool : Type :=
  | true : bool
  | false : bool.


(* Compound Types *)
Inductive rgb : Type := 
  | red : rgb
  | green : rgb
  | blue : rgb.

Inductive color : Type :=
  | black : color
  | white : color
  | primary : rgb -> color.

Check red.

(* 如果 p 属于集合 rgb, 则 primary p 属于集合 color *)

Definition monochrome (c : color) : bool := 
  match c with
  | black => true
  | white => true
  | primary p => false
  end.

Example test_monochrome1: (monochrome black) = true.
Proof. simpl. reflexivity. Qed.
Example test_monochrime2: (monochrome white) = true.
Proof. simpl. reflexivity. Qed.
Example test_monochrime3: (monochrome (primary red)) = false.
Proof. simpl. reflexivity. Qed.

Definition isred (c : color) : bool :=
  match c with
  | black => false
  | white => false
  | primary red => true
  | primary _ => false
  end.

Example test_isred1: ( isred black ) = false.
Proof. simpl. reflexivity. Qed.
Example test_isred2: ( isred white ) = false.
Proof. simpl. reflexivity. Qed.
Example test_isred3: ( isred (primary red) ) = true.
Proof. simpl. reflexivity. Qed.
Example test_isrea4: ( isred (primary blue) ) = false.
Proof. simpl. reflexivity. Qed.

Module NatPlayground.

(*
1. O 是一个自然数
2. S 提供一个自然数 n 可以产生下一个自然数，也就是说 n 是一个自然数的话, S n 也是一个自然数
*)

Inductive nat : Type :=
  | O : nat
  | S : nat -> nat.

Definition pred (n : nat) : nat :=
  match n with
  | O => O
  | S n' => n'
  end.
Example test_pred1: ( pred O ) = O.
Proof. simpl. reflexivity. Qed.
Example test_pred2: ( pred (S O) ) = O.
Proof. simpl. reflexivity. Qed.
Example test_pred3: ( pred (S (S O)) ) = S O.
Proof. simpl. reflexivity. Qed.
Example test_pred4: ( pred (S (S (S O))) ) = (S (S O)).
Proof. simpl. reflexivity. Qed.

End NatPlayground.

Check (S (S (S O))).
