(* Exercicio - IndProp.v - Lista 8
   Nome: Geremias Corrêa      *)
Set Warnings "-notation-overridden,-parsing".
(*From LF Require Export Logic.*)

(*####### IMPORTS NECESSÁRIOS ########*)


Inductive even : nat -> Prop :=
| ev_0 : even 0
| ev_SS (n : nat) (H : even n) : even (S (S n)).

Inductive even' : nat -> Prop :=
| even'_0 : even' 0
| even'_2 : even' 2
| even'_sum n m (Hn : even' n) (Hm : even' m) : even' (n + m).

Theorem ev_sum : forall n m, even n -> even m -> even (n + m).
Proof.
  intros n m N M. induction N as [|n' N'].
  - simpl. assumption.
  - simpl. apply ev_SS. assumption.
Qed.

Theorem ev_inversion :
  forall (n : nat), even n ->
    (n = 0) \/ (exists n', n = S (S n') /\ even n').
Proof.
  intros n E.
  destruct E as [ | n' E'].
  - left. reflexivity.
  - right. exists n'. split. reflexivity. apply E'.
Qed.

Theorem evSS_ev : forall n, even (S (S n)) -> even n.
Proof. intros n H. apply ev_inversion in H. destruct H.
 - discriminate H.
 - destruct H as [n' [Hnm Hev]]. injection Hnm.
   intro Heq. rewrite Heq. apply Hev.
Qed.

Theorem plus_comm : forall n m : nat,
  n + m = m + n.
Proof.
  intros n m. induction n as [| n' IHn'].
  - simpl. rewrite <- plus_n_O. reflexivity.
  - rewrite <- plus_n_Sm. rewrite <- IHn'. reflexivity.
Qed.

Theorem plus_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p. induction n as [|n' IHn'].
  - reflexivity.
  - simpl. rewrite <- IHn'. reflexivity.
Qed.

Theorem plus_swap : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
  intros n m p.
  rewrite -> plus_assoc.
  assert (H: n + m = m + n). rewrite -> plus_comm. reflexivity. rewrite -> H.
  rewrite -> plus_assoc. reflexivity.
Qed.

Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

Lemma double_plus : forall n, double n = n + n .
Proof.
  intros n. induction n as [ | n' IHn'].
  - reflexivity.  (* caso 0 = 0 * 0*)
  - simpl. rewrite -> IHn'. rewrite -> plus_n_Sm. reflexivity.
Qed.

Theorem ev_double : forall n,
  even (double n).
Proof.
  intros n. rewrite double_plus. induction n as [| n'].
  - simpl. apply ev_0.
  - simpl. rewrite <- plus_n_Sm. apply ev_SS. apply IHn'.
Qed.    

Inductive le : nat -> nat -> Prop :=
  | le_n n : le n n
  | le_S n m (H : le n m) : le n (S m).

Notation "m <= n" := (le m n).

(*3 dessas 4 importadas abaixo são do arquivo professor do Moodle*)
(*A primeira logo abaixo é a que já vinha para resolução da questão, botei aqui para poder usar a le'_n_n*)

Inductive le' : nat -> nat -> Prop :=
  | le_0' m : le' 0 m
  | le_S' n m (H : le' n m) : le' (S n) (S m).

Lemma le'_n_n : forall a, le' a a.
Proof.
  intros a. induction a as [|a' IH].
  + apply le_0'.
  + apply le_S'. apply IH.
Qed.

Lemma le'_n_Sm : forall a b, le' a b -> le' a (S b). 
Proof.
  intros a b H. induction H as [|a' b' Hab IH].
  - apply le_0'.
  - apply le_S'. apply IH.
Qed. 

Theorem n_le'_m__Sn_le'_Sm : forall a b, le' a b -> le' (S a) (S b).
Proof.
  intros a b H. induction H as [m | n m Hnm IHnm].
  - apply le_S'. apply le_0'.
  - apply le_S'. apply IHnm.
Qed.

Theorem n_le_m__Sn_le_Sm : forall a b, le a b -> le (S a) (S b).
Proof.
  Admitted.
 (*Não consegui provar essa, então dei um admitted para conseguir finalizar a le_le'.*)


(*##### FIM IMPORTS NECESSÁRIOS ######*)

(* 1 - Prove que as definições even e even' são equivalentes *)
Theorem even'_ev : forall n, even' n <-> even n.
Proof.
  intros n. split.
  - intros E. induction E. 
    + apply ev_0.
    + apply ev_SS. apply ev_0.
    + apply ev_sum. assumption. assumption.
  - intros E. induction E.
    + apply even'_0.
    + assert (S (S n) = 2 + n) as H.
      * induction n.
        -- reflexivity.
        -- reflexivity.
      * rewrite H. apply even'_sum.
       -- apply even'_2.
       -- assumption.
Qed.

(* 2 - Prove que se a soma de dois naturais é um numero par e
       o primeiro numero é par implkca que os dois números são pares. *)
Theorem ev_ev__ev : forall n m,
  even (n + m) -> even n -> even m.
Proof.
  intros n m H0 H1. induction H1.
  - assumption.
  - apply IHeven. assert (S (S n) + m = S (S (n + m))) as H.
    + reflexivity.
    + rewrite H in H0. apply evSS_ev in H0. assumption.
Qed.
(*professor fez uso do inversion, que é para ser utilizada sobre tipos indutivos, ela junta algumas táticas, como discrimante etc*)

(* 3 - Prove: *)

Theorem ev_plus_plus : forall n m p,
  even (n+m) -> even (n+p) -> even (m+p).
Proof.
  intros n m p H1.
  assert (even (n+m) -> even ((n+p)+(m+p))) as H.
    - intros H. rewrite (plus_comm n p). rewrite (plus_comm m p). rewrite plus_swap.
    rewrite plus_assoc. rewrite plus_assoc. rewrite <- double_plus.
    rewrite <- (plus_assoc (double p) n m). apply ev_sum. apply ev_double. apply H1.
    - apply H in H1. apply (ev_ev__ev (n+p)). assumption.
Qed.

(* 4 - Prove que zero é menor ou igual a qualquer número natural *)

Theorem O_le_n : forall n,
  0 <= n.
Proof.
  intros n. induction n.
  - apply le_n.
  - apply le_S. assumption.
Qed.

(* 5 - Prove que a relação menor ou igual é transitiva *)

Lemma le_trans : forall m n o, m <= n -> n <= o -> m <= o.
Proof.
  intros m n o Hmn Hno. induction Hno as [|n' o'].
  - apply Hmn.
  - apply le_S. apply IHHno. apply Hmn.
Qed.

(* 6 - Prove que a relação definida pelo tipo le' é equivalente
       a relação <= *)

(*Obs: Essa 6 eu não consegui direito, mas usei a resolução da prova do professor para tentar interpretar eentender (os auxiliares), ainda sim gerando problemas no final*)
(*Ainda sim geraram problemas, precisei dar um admitted e isso aí.*)

Theorem le_le' : forall a b, le a b <-> le' a b.
Proof.
  intros a b. split.
  - intros H. induction H.
    + apply le'_n_n.
    + apply le'_n_Sm. apply IHle.
  - intros H. induction H.
    + apply O_le_n.
    + apply n_le_m__Sn_le_Sm. apply IHle'. 
Qed.












