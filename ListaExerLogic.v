From LF Require Export Logic.

Theorem or_distributes_over_and : forall P Q R : Prop,
  P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
  Admitted.

(*Essa não tem na lista lá, todas as outras tem resolvidas no github lá*)
Theorem dist_exists_and : forall (X:Type) (P Q : X -> Prop),
  (exists x, P x /\ Q x) -> (exists x, P x) /\ (exists x, Q x).
Proof.
 Admitted.

Lemma In_map_iff :
  forall (A B : Type) (f : A -> B) (l : list A) (y : B),
    In y (map f l) <->
    exists x, f x = y /\ In x l.
Proof.
  Admitted.

Lemma In_app_iff : forall A l l' (a:A),
  In a (l++l') <-> In a l \/ In a l'.
Proof.
 Admitted.

(* Inspirado na função [In], defina uma função [All] que é válida quando
uma proposição [P] é válida para todos elementos de uma lista [l]: *) 

Fixpoint All {T : Type} (P : T -> Prop) (l : list T) : Prop.


Lemma All_In :
  forall T (P : T -> Prop) (l : list T),
    (forall x, In x l -> P x) <->
    All P l.
Proof.
  Admitted.

  

