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


Definition negb (b: bool) : bool :=
	match b with
	| true => false
	| false => true
	end.

Definition andb (b1: bool) (b2: bool) : bool :=
	match b1 with
	| true => b2
	| false => false
	end.

Definition orb (b1: bool) (b2: bool) : bool :=
	match b1 with
	| true => true
	| false => b2
	end.

Notation "x && y" := (andb x y).
Notation "x || y" := (orb x y).

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
Check (O).
Check (S (S (S O))).

Definition minustwo (n : nat) : nat :=
  match n with
    | O => O
    | S O => O
    | S (S n') => n' (* S (S n') 减去 外面两层，得到内层 n' *)
  end.

Compute (minustwo 7).

Check S.
Check pred.
Check minustwo.

Fixpoint evenb (n : nat) : bool :=
  match n with
    | O => true
    | S O => false
    | S (S n') => evenb n'
  end.

Definition oddb (n : nat) : bool := negb (evenb n).

Example test_oddb1 : oddb 1 = true.
Proof. simpl. reflexivity. Qed.
Example test_oddb2 : oddb 4 = false.
Proof. simpl. reflexivity. Qed.


Module NatPlayground2.
  (*
    计算过程演算
    Compute plus (S (S( S O))) (S (S O))
    1. (S plus (S (S O)) (S (S O)))
    2. (S (S (plus (S O) (S (S O)))))
    3. (S (S (S (plus O (S (S O)))))
    4. (S (S (S (S (S O))))) 结束.
  *)
  Fixpoint plus (n : nat) (m : nat) :=
    match n with
      | O => m
      | S n' => S ( plus n' m )
    end.
  Compute (plus 3 2).

  Fixpoint mult (n m : nat) :=
    match n with
      | O => O
      | S n' => plus m ( mult n' m )
    end.

  Fixpoint minus (n m : nat) :=
    match n, m with
      | O, _ => O
      | S _, O => n
      | S n', S m' => minus n' m'
    end.
  Example test_mult1: (mult 3 3) = 9.
  Proof. simpl. reflexivity. Qed.
  Example test_minus1: (minus 9 3) = 6.
  Proof. simpl. reflexivity. Qed.
  
End NatPlayground2.

Fixpoint exp (base power : nat) : nat :=
    match power with
      | O => S O (* 任意自然数的一次方等于 1 *)
      | S p => mult base (exp base p)
    end.

Fixpoint factorial (n : nat) : nat :=
  match n with
    | O => S O
    | S n' => mult n (factorial n')
  end.

Example test_factorial1: (factorial 5) = (mult 10 12).
Proof. simpl. reflexivity. Qed.

Notation "x + y" :=
  (plus x y)
  (at level 50, left associativity)
  : nat_scope.

Notation "x - y" :=
  (minus x y)
  (at level 50, left associativity)
  : nat_scope.

Notation "x * y" :=
  (mult x y)
  (at level 40, left associativity)
  : nat_scope.

Check ( (0 + 1) + 1 ).

Fixpoint beq_nat (n m : nat) : bool :=
  match n with
    | O => match m with
            | O => true
            | S m' => false
            end
    | S n' => match m with
              | O => false
              | S m' => beq_nat n' m'
              end
    end.

Compute ( beq_nat 12 12 ).

Fixpoint leb (n m : nat) : bool :=
  match n with
  | O => true
  | S n' => match m with
            | O => false
            | S m' => leb n' m'
            end
  end.

Example test_leb1: (leb 2 2) = true.
Proof. simpl. reflexivity. Qed.
Example test_leb2: (leb 2 4) = true.
Proof. simpl. reflexivity. Qed.
Example test_leb3: (leb 4 2) = false.
Proof. simpl. reflexivity. Qed.

(*Exercise: 1 star (blt nat)*)
Fixpoint blt_nat (n m : nat) : bool :=
  match n, m with
  | O, O => false
  | O, _ => true
  | _, O => false
  | S n', S m' => blt_nat n' m'
  end. 

Example test_blt_nat1: (blt_nat 2 2) = false.
Proof. simpl. reflexivity. Qed.
Example test_blt_nat2: (blt_nat 2 4) = true.
Proof. simpl. reflexivity. Qed.
Example test_blt_nat3: (blt_nat 4 2) = false.
Proof. simpl. reflexivity. Qed.

Theorem plus_0_n: forall n : nat, O + n = n.
Proof.
  intros n. simpl. reflexivity. Qed.
  
  