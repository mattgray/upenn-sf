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

Eval simpl in (next_weekday friday).

Example test_next_weekday:
(next_weekday (next_weekday saturday)) = tuesday.

Proof. simpl. reflexivity. Qed.

Inductive bool : Type :=
| true : bool
| false : bool.

Definition negb (b:bool) : bool := 
match b with
| true => false
| false => true
end.

Definition andb (b1:bool) (b2:bool) : bool := 
match b1 with
| true => b2
| false => false
end.


Definition orb (b1:bool) (b2:bool) : bool := 
match b1 with
| true => true
| false => b2
end.


Example test_orb1: (orb true false) = true.
Proof. simpl. reflexivity. Qed.
Example test_orb2: (orb false false) = false.
Proof. simpl. reflexivity. Qed.
Example test_orb3: (orb false true ) = true.
Proof. simpl. reflexivity. Qed.
Example test_orb4: (orb true true ) = true.
Proof. simpl. reflexivity. Qed.


Definition admit {T: Type} : T. Admitted.

Definition nandb (b1:bool) (b2:bool) : bool :=
match b1 with
| false => true
| true => negb b2
end.


Example test_nandb1: (nandb true false) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb2: (nandb false false) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb3: (nandb false true) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb4: (nandb true true) = false.
Proof. simpl. reflexivity. Qed.

Definition andb3 (b1:bool) (b2:bool) (b3:bool) : bool :=
match b1 with
| true => andb b2 b3
| false => false
end.

Example test_andb31: (andb3 true true true) = true.
Proof. simpl. reflexivity. Qed.
Example test_andb32: (andb3 false true true) = false.
Proof. simpl. reflexivity. Qed.
Example test_andb33: (andb3 true false true) = false.
Proof. simpl. reflexivity. Qed.
Example test_andb34: (andb3 true true false) = false.
Proof. simpl. reflexivity. Qed.

Check (negb true).
Check negb.


(* natural numbers *)

Module Scratch1.

Inductive nat : Type :=
| O : nat
| S : nat -> nat.

Definition pred (n : nat) : nat := 
match n with
| O => O
| S n' => n'
end.

End Scratch1.

Definition minustwo (n : nat) : nat :=
  match n with
    | O => O
    | S O => O
    | S (S n') => n'
  end.

Check (S (S (S (S O)))).

Eval simpl in (minustwo 4).

Fixpoint evenb (n:nat) : bool :=
match n with
| O => true
| S O => false
| S (S n') => evenb n'
end.











































