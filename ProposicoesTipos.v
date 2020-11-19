(*Lista de exercícios 7, exercícios Proj2, Sum1, Sum2 e Case*)
(*Autor: Geremias Corrêa*)
(*Obs: outros exercícios feitos em sala contidos nele também*)

Theorem Var : forall A : Prop, A -> A. (*tática VAR*)
  Proof.
    intros A x. apply x.
Qed.

Print Var.

Definition Var' (A : Prop) (x : A) := x.

Print Var'.

Theorem App : forall (A B : Prop), (A -> B) -> A -> B. (*tática APP*)
  (*Se (A->B) é verdade, então A -> B é verdade*)
  Proof. 
    intros A B e e'. apply e. apply e'. (*unifica B com A, para provar A*)
Qed.

Print App.

Definition App' (A B : Prop) (e : A -> B) (e' : A) := e e'.

Print App'.

Theorem Abs : forall (A B : Prop), B -> (A -> B). (*Tática ABS*)
  (* Se B é verdade, então A -> B é verdade*)
  Proof.
    intros A B e H. apply e.
Qed.

Print Abs. 

Definition Abs' (A B : Prop) (e : B) := fun (x : A) => e.

Print Abs'.


Theorem Prod : forall (A B : Prop), A -> B -> A /\ B. (*Tática PROD*)
(*Se A - > B é verdade, então A e B são verdade*)
  Proof.
    intros A B e e'. split.
    - apply e.
    - apply e'.
Qed.

Print Prod. 

(*Aqui ele mesmo gera o código da tática*)
Definition Prod' (A B : Prop) (e : A) (e' : B) := conj e e'.

Print Prod'.

Theorem Proj1 : forall (A B : Prop), A /\ B -> A.
  intros A B H. destruct H as [e e']. apply e.
Qed.

Print Proj1.

Definition Proj1' (A B : Prop ) (H : A /\ B) := 
  match H with 
  | conj e e' => e
  end.

Print Proj1'.

(*Resolução da lista 7 de mfo*)
(*Questão 1 - Proj2*)
Theorem Proj2 : forall (A B : Prop), A /\ B -> B.
  intros A B H. destruct H as [e e']. apply e'. Qed.

Print Proj2.

Definition Proj2' (A B : Prop) (H : A /\ B) :=
  match H with
  | conj e e' => e'
  end.

Print Proj2'.

(*Questão 2 - Sum1*) 
Theorem Sum1: forall (A B : Prop), A -> A \/ B.
  intros A B e. left. apply e. Qed.
 
Print Sum1.
 
(*Obs: seguindo a risca o print Sum1 não funfa! Mesmo para Sum2*)
Definition Sum1' (A B : Prop) (e : A) : A \/ B :=
  or_introl e.

Print Sum1'.

(*Questão 3 - Sum2*)
Theorem Sum2: forall (A B : Prop), B -> A \/ B.
  intros A B e. right. apply e. Qed.
 
Print Sum2.
 
Definition Sum2' (A B : Prop) (e : B) : A \/ B :=
  or_intror e.

Print Sum2'.

(*Questão 4 - Case*)
Theorem Case: forall (A B C : Prop), (A -> C) -> (B -> C) -> (A \/ B) -> C.
  intros A B C H1 H2 H3. destruct H3. apply H1. apply H. apply H2. apply H. Qed.

Print Case.

Definition Case' (A B C : Prop) (H1 : A -> C) (H2 : B -> C) (H3 : A \/ B) :=
match H3 with
| or_introl H => H1 H
| or_intror H => H2 H
end.

Print Case'.



